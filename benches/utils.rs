use criterion::Criterion;

#[cfg(unix)]
pub fn make_criterion() -> Criterion {
    use pprof::criterion::{Output, PProfProfiler};
    Criterion::default()
        .with_profiler(PProfProfiler::new(1000, Output::Flamegraph(None)))
        .configure_from_args()
}

#[cfg(not(unix))]
pub fn make_criterion() -> Criterion {
    Criterion::default().configure_from_args()
}
