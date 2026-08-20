from pathlib import Path
import os
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


def _find_lake():
    lake = shutil.which("lake")
    if lake is not None:
        return lake
    candidates = (
        Path.home() / ".elan" / "bin" / "lake",
        Path.home() / ".local" / "bin" / "lake",
        Path("/usr/local/bin/lake"),
        Path("/usr/bin/lake"),
    )
    lake_path = next((path for path in candidates if path.is_file()), None)
    return str(lake_path) if lake_path is not None else None


def test_lean_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    proc = subprocess.run(
        [lake, "build"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]


def test_all_lean_modules_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    lean_files = [root / "ZetaZero.lean"]
    lean_files.extend(sorted((root / "ZetaZero").rglob("*.lean")))
    targets = [
        path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
        for path in lean_files
    ]
    proc = subprocess.run(
        [lake, "build", *targets],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]


def test_mainline_hardy_stationary_bridge_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    proc = subprocess.run(
        [
            lake,
            "build",
            "ZetaZero.HardyGaugeInvariantContourForm",
            "ZetaZero.ZeroSideStationaryGeometry",
            "ZetaZero.HardyGaugeInvariantContourForm.Zeta23HardyBridge",
            "ZetaZero.Analytic.ZetaOneCounting",
            "ZetaZero.ZeroSideStationaryGeometry.StationarySourceBridge",
            "ZetaZero.ZeroSideStationaryGeometry.StationaryDictionary",
            "ZetaZero.ZeroSideStationaryGeometry.EvaluationPullback",
        ],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]


def test_previous_unverified_modules_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    proc = subprocess.run(
        [
            lake,
            "build",
            "ZetaZero.FrameCompression.FiniteFeatureRank",
            "ZetaZero.FrameCompression.TranslatedPoleFeatureRank",
            "ZetaZero.HLPLocalModel.LeadingJetResummation",
        ],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]


def test_hlp_mean_square_recurrence_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    proc = subprocess.run(
        [
            lake,
            "build",
            "ZetaZero.HLPLocalModel.MeanSquareRecurrence",
            "ZetaZero.HLPLocalModel.AlphaFactorialMajorant",
            "ZetaZero.HLPLocalModel.FiniteDirectCarrier",
            "ZetaZero.HLPLocalModel.FactorialLevelSummability",
            "ZetaZero.HLPLocalModel.ResolventTailBound",
            "ZetaZero.HLPLocalModel.ZetaPoleLaurentBridge",
            "ZetaZero.HLPLocalModel",
        ],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]


def test_stationary_oscillatory_approximation_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    proc = subprocess.run(
        [
            lake,
            "build",
            "ZetaZero.RightEdgeArithmeticSource.StationaryOscillatoryApproximation",
            "ZetaZero.RightEdgeArithmeticSource.StationaryMainTermError",
        ],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]


def test_gcd_gram_identity_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    proc = subprocess.run(
        [
            lake,
            "build",
            "ZetaZero.DivisorGramArithmeticTransfer.GcdGramIdentity",
            "ZetaZero.DivisorGramArithmeticTransfer.OperatorGcdGramLift",
            "ZetaZero.DivisorGramArithmeticTransfer",
        ],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]


def test_global_model_floor_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    proc = subprocess.run(
        [lake, "build", "ZetaZero.GlobalModelSpectralFloor"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]



def test_fixed_edge_range_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    proc = subprocess.run(
        [lake, "build", "ZetaZero.FrameCompression"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]



def test_straightening_bridge_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    proc = subprocess.run(
        [lake, "build", "ZetaZero.ZeroSideStationaryGeometry.StraighteningBridge"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]


def test_density_one_endgame_interface_build():
    root = Path(__file__).resolve().parent
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    proc = subprocess.run(
        [lake, "build", "ZetaZero.GenericPerturbationMinMaxEndgame.DensityOne"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]



def test_blueprint_declarations():
    root = Path(__file__).resolve().parent
    leanblueprint = root / "blueprint" / ".venv" / "bin" / "leanblueprint"
    assert leanblueprint.is_file(), "leanblueprint is not installed in blueprint/.venv"
    lake = _find_lake()
    assert lake is not None, "lake is not installed or not discoverable"
    env = os.environ.copy()
    env["PATH"] = f"{Path(lake).parent}:{env.get('PATH', '')}"
    proc = subprocess.run(
        [str(leanblueprint), "checkdecls"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=180,
        env=env,
    )
    assert proc.returncode == 0, proc.stdout[-20000:]


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
