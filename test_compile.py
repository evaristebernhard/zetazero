from pathlib import Path
import shutil
import subprocess


def test_global_floor_certificate():
    root = Path(__file__).resolve().parent
    proc = subprocess.run(
        ["python3", "verify_global_floor.py"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=120,
    )
    assert proc.returncode == 0, proc.stdout
    assert "PASS" in proc.stdout


def test_source_profile_symbolic_certificate():
    root = Path(__file__).resolve().parent
    proc = subprocess.run(
        ["python3", "verify_profile_symbolic.py"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=120,
    )
    assert proc.returncode == 0, proc.stdout
    assert "PASS" in proc.stdout


def test_canonical_proof_guards():
    root = Path(__file__).resolve().parent
    tex_paths = [root / "main.tex"]
    sections = root / "sections"
    if sections.exists():
        tex_paths.extend(sorted(sections.glob("*.tex")))
    tex = "\n".join(path.read_text(errors="replace") for path in tex_paths)

    required = (
        r"\boxed{A_T^G\succeq0.06\,\Gfr_T.}",
        r"\boxed{P_T\succeq c_0\Gfr_T}",
        r"dm=en=:N",
        r"\label{eq:principal-finiteT-comparison}",
        r"\label{eq:minmax-good-space}",
        r"\label{eq:levelwise-PP-projector}",
        r"\label{eq:model-principal-cluster}",
        r"\label{eq:arithmetic-two-sided-transfer}",
        r"\label{eq:packet-bandwidth-reserve}",
        r"\label{eq:outer-excess-edge-rank}",
        r"\label{eq:N-common-core}",
        r"\label{eq:Hex-variable}",
        r"\label{lem:block-freezing}",
        r"\label{eq:mu-lambda-close}",
        r"0<\kappa<\frac1{10}",
    )
    missing = [needle for needle in required if needle not in tex]
    assert not missing, f"canonical proof text missing: {missing}"

    forbidden = (
        "Soft spectral floor for the completed model",
        "V_G",
        "model-bad-codim",
        r"\eqref{eq:G-profile}",
        r"V_{\rm block}",
        r"V_{\rm shell}",
        r"\label{eq:shell-codim}",
        r"V_{\rm frame}",
        r"\label{eq:fourier-trim-floor}",
        r"\Sigma_0^{\rm ex}",
        r"\kappa<\frac13",
        "subtracts a nonnegative outer displacement",
        "completed carrier endpoint is shortened",
        "two logarithmic fibre trims",
        r"F_b=f(\tau)",
    )
    stale = [needle for needle in forbidden if needle in tex]
    if stale:
        locations = {
            needle: tex[: tex.index(needle)].count("\n") + 1
            for needle in stale
        }
        raise AssertionError(f"stale proof branch reintroduced: {locations}")

    assert tex.count(r"\end{document}") == 1, "main.tex must have exactly one end-of-document marker"


def test_main_tex_compiles_cleanly():
    root = Path(__file__).resolve().parent
    engine = shutil.which("pdflatex")
    assert engine is not None, "pdflatex is not installed"

    output = ""
    for _ in range(3):
        proc = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=120,
        )
        output = proc.stdout
        assert proc.returncode == 0, output[-12000:]

    pdf = root / "main.pdf"
    log = root / "main.log"
    assert pdf.exists()
    assert log.exists()

    log_text = log.read_text(errors="replace")
    forbidden = (
        "Undefined control sequence",
        "LaTeX Warning:",
        "Package hyperref Warning:",
        "Overfull \\hbox",
        "Overfull \\vbox",
    )
    bad = [needle for needle in forbidden if needle in log_text]
    assert not bad, f"LaTeX diagnostics present: {bad}\n{output[-12000:]}"
