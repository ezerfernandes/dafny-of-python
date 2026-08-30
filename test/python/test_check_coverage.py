import io
import runpy
import sys
import warnings

from scripts import check_coverage


def test_project_pair_reads_only_the_aggregate():
    summary = "src/a.ml 10/10\nProject coverage: 20/20\n"
    assert check_coverage.project_pair(summary) == (20, 20)


def test_project_pair_rejects_missing_or_ambiguous_aggregate():
    assert check_coverage.project_pair("src/a.ml 10/10\n") is None
    assert check_coverage.project_pair("Project coverage: 20/20 99/100\n") is None


def run_main(summary, monkeypatch, capsys):
    monkeypatch.setattr(sys, "stdin", io.StringIO(summary))
    code = check_coverage.main()
    captured = capsys.readouterr()
    return code, captured.out, captured.err


def test_main_accepts_exact_coverage(monkeypatch, capsys):
    code, output, errors = run_main("Project coverage: 100/100\n", monkeypatch, capsys)
    assert code == 0
    assert "100/100" in output
    assert errors == ""


def test_main_rejects_missing_and_empty_coverage(monkeypatch, capsys):
    code, _, errors = run_main("not a report\n", monkeypatch, capsys)
    assert code == 2
    assert "no covered/total" in errors

    code, _, errors = run_main("Project coverage: 0/0\n", monkeypatch, capsys)
    assert code == 2
    assert "no instrumentation" in errors


def test_main_rejects_coverage_at_or_below_threshold(monkeypatch, capsys):
    code, _, errors = run_main("Project coverage: 95/100\n", monkeypatch, capsys)
    assert code == 1
    assert "must be above 95%" in errors


def test_script_entry_point(monkeypatch, capsys):
    monkeypatch.setattr(sys, "stdin", io.StringIO("Project coverage: 100/100\n"))
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", RuntimeWarning)
        try:
            runpy.run_module("scripts.check_coverage", run_name="__main__")
        except SystemExit as raised:
            assert raised.code == 0
        else:
            raise AssertionError("the script entry point should exit")
    assert "100/100" in capsys.readouterr().out
