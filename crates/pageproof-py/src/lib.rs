//! Python facade for the verified block manager. UNVERIFIED, part of the trusted I/O shim.
//!
//! This file only converts between Python objects and the verified API. It never touches
//! manager state directly, never recomputes addresses, and never constructs a `Completion` for a
//! ticket other than the one the caller names. All allocation, caching, and protocol logic lives
//! in `pageproof-core` and is proved there.
use pageproof_core::manager::Manager;
use pageproof_core::ops_write::Completion;
use pageproof_core::types::{Error, Handle, Ticket};
use pyo3::exceptions::PyException;
use pyo3::prelude::*;

pyo3::create_exception!(pageproof, BlockManagerError, PyException);

fn err(e: Error) -> PyErr {
    BlockManagerError::new_err(format!("{e:?}"))
}

/// Request lease handle (opaque).
#[pyclass(frozen, eq, hash, from_py_object)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct PyHandle {
    mgr: u64,
    id: u64,
}

/// Execution ticket (opaque).
#[pyclass(frozen, eq, hash, from_py_object)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct PyTicket {
    mgr: u64,
    id: u64,
}

impl From<Handle> for PyHandle {
    fn from(h: Handle) -> Self {
        PyHandle { mgr: h.mgr, id: h.id }
    }
}

impl From<PyHandle> for Handle {
    fn from(h: PyHandle) -> Self {
        Handle { mgr: h.mgr, id: h.id }
    }
}

impl From<Ticket> for PyTicket {
    fn from(t: Ticket) -> Self {
        PyTicket { mgr: t.mgr, id: t.id }
    }
}

impl From<PyTicket> for Ticket {
    fn from(t: PyTicket) -> Self {
        Ticket { mgr: t.mgr, id: t.id }
    }
}

/// Immutable execution plan (contract C3).
#[pyclass(frozen, get_all)]
struct Plan {
    ticket: PyTicket,
    handle: PyHandle,
    input_ids: Vec<u32>,
    positions: Vec<usize>,
    write_slots: Vec<usize>,
    page_table: Vec<usize>,
    block_size: usize,
}

#[pyclass(name = "BlockManager", unsendable)]
struct PyBlockManager {
    inner: Manager,
}

#[pymethods]
impl PyBlockManager {
    #[new]
    fn new(num_pages: usize, block_size: usize, namespace: &[u8]) -> PyResult<Self> {
        Manager::create(num_pages, block_size, namespace).map(|inner| PyBlockManager { inner }).map_err(err)
    }

    #[getter]
    fn block_size(&self) -> usize {
        self.inner.block_size()
    }

    #[getter]
    fn num_pages(&self) -> usize {
        self.inner.num_pages()
    }

    #[getter]
    fn free_pages(&self) -> usize {
        self.inner.free_count()
    }

    /// C1. Returns `(handle, cached_tokens, page_table)`.
    fn attach(&mut self, tokens: Vec<u32>) -> PyResult<(PyHandle, usize, Vec<usize>)> {
        let (h, cached, view) = self.inner.attach(&tokens).map_err(err)?;
        Ok((h.into(), cached, view.pages))
    }

    /// C2. Returns the new page table.
    fn extend(&mut self, handle: PyHandle, suffix: Vec<u32>) -> PyResult<Vec<usize>> {
        self.inner.extend(handle.into(), &suffix).map(|v| v.pages).map_err(err)
    }

    /// C3.
    fn begin_write(&mut self, handle: PyHandle, n: usize) -> PyResult<Plan> {
        let (_, p) = self.inner.begin_write(handle.into(), n).map_err(err)?;
        Ok(Plan {
            ticket: p.ticket.into(),
            handle: p.handle.into(),
            input_ids: p.input_ids,
            positions: p.positions,
            write_slots: p.write_slots,
            page_table: p.page_table,
            block_size: p.block_size,
        })
    }

    /// C4. The caller (executor) asserts that `ticket`'s plan has been executed (E1/E2/E5).
    fn finish_write(&mut self, ticket: PyTicket) -> PyResult<usize> {
        let t: Ticket = ticket.into();
        self.inner.finish_write(t, Completion { ticket: t }).map_err(err)
    }

    /// C5. Returns the lease's token snapshot.
    fn release(&mut self, handle: PyHandle) -> PyResult<Vec<u32>> {
        self.inner.release(handle.into()).map_err(err)
    }

    /// C6. Returns a dict view.
    fn inspect<'py>(&self, py: Python<'py>, handle: PyHandle) -> PyResult<Bound<'py, pyo3::types::PyDict>> {
        let v = self.inner.inspect(handle.into()).map_err(err)?;
        let d = pyo3::types::PyDict::new(py);
        d.set_item("len", v.len)?;
        d.set_item("computed", v.computed)?;
        d.set_item("pages", v.pages)?;
        d.set_item("pending", v.pending.map(PyTicket::from))?;
        d.set_item("block_size", v.block_size)?;
        Ok(d)
    }

    /// C6 `slot_of`.
    fn slot_of(&self, handle: PyHandle, j: usize) -> PyResult<usize> {
        self.inner.slot_of(handle.into(), j).map_err(err)
    }
}

#[pymodule]
fn pageproof(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyBlockManager>()?;
    m.add_class::<PyHandle>()?;
    m.add_class::<PyTicket>()?;
    m.add_class::<Plan>()?;
    m.add("BlockManagerError", m.py().get_type::<BlockManagerError>())?;
    Ok(())
}
