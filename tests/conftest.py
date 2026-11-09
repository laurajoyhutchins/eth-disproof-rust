"""Test-tier enforcement and useful machine-readable collection metadata."""
import pytest

PRIMARY = frozenset(('checkpoint', 'integration', 'extended', 'benchmark'))


def pytest_collection_modifyitems(items):
    wrong=[]
    for test in items:
        tags={mark.name for mark in test.iter_markers() if mark.name in PRIMARY}
        if len(tags)!=1:
            wrong.append(f"{test.nodeid}: expected one primary tier, got {sorted(tags)}")
    if wrong:
        raise pytest.UsageError("Test tier classification failure:\n" + "\n".join(wrong))


# Optional libraries are legitimate skips for a plain checkpoint, but are
# mandatory coverage when a change to that backend is under review.
BACKEND_MARKERS = {"flint": "requires_flint", "ganak": "requires_ganak",
                   "native": "requires_native"}


def pytest_addoption(parser):
    parser.addoption("--require-backend", action="append", default=[],
                     choices=sorted(BACKEND_MARKERS),
                     help="Require actual, non-skipped tests for this backend")


def pytest_runtest_logreport(report):
    if report.when not in ("setup", "call"):
        return
    for backend, marker in BACKEND_MARKERS.items():
        if marker in report.keywords:
            report_map = _ACTIVE_BACKEND_REPORTS
            if report.outcome in ("passed", "skipped", "failed"):
                report_map.setdefault(backend, {})[report.nodeid] = report.outcome


_ACTIVE_BACKEND_REPORTS = {}


def pytest_sessionstart(session):
    _ACTIVE_BACKEND_REPORTS.clear()


def pytest_sessionfinish(session, exitstatus):
    required = session.config.getoption("--require-backend")
    for backend in required:
        outcomes = _ACTIVE_BACKEND_REPORTS.get(backend, {})
        if not outcomes or any(x != "passed" for x in outcomes.values()):
            reporter = session.config.pluginmanager.get_plugin("terminalreporter")
            if reporter is not None:
                reporter.write_line(
                    f"REQUIRED BACKEND {backend}: no tests, skips, or failures: {outcomes}",
                    red=True)
            session.exitstatus = pytest.ExitCode.TESTS_FAILED
