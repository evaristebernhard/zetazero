import sys
import traceback
from test_compile import (
    test_all_lean_modules_build,
    test_blueprint_declarations,
    test_canonical_proof_guards,
    test_global_floor_certificate,
    test_gcd_gram_identity_build,
    test_lean_build,
    test_hlp_mean_square_recurrence_build,
    test_mainline_hardy_stationary_bridge_build,
    test_previous_unverified_modules_build,
    test_straightening_bridge_build,
    test_main_tex_compiles_cleanly,
    test_source_profile_symbolic_certificate,
)


def main():
    all_tests = {
        "global-floor": test_global_floor_certificate,
        "source-profile": test_source_profile_symbolic_certificate,
        "proof-guards": test_canonical_proof_guards,
        "lean": test_lean_build,
        "lean-all": test_all_lean_modules_build,
        "hlp-meansquare": test_hlp_mean_square_recurrence_build,
        "gcd-gram": test_gcd_gram_identity_build,
        "mainline-bridge": test_mainline_hardy_stationary_bridge_build,
        "previous-unverified": test_previous_unverified_modules_build,
        "straightening": test_straightening_bridge_build,
        "blueprint-decls": test_blueprint_declarations,
        "latex": test_main_tex_compiles_cleanly,
    }
    if len(sys.argv) > 1:
        unknown = [name for name in sys.argv[1:] if name not in all_tests]
        if unknown:
            raise SystemExit(f"unknown test selector(s): {', '.join(unknown)}")
        tests = tuple(all_tests[name] for name in sys.argv[1:])
    else:
        tests = tuple(all_tests.values())
    for test in tests:
        try:
            test()
        except Exception:
            traceback.print_exc()
            raise SystemExit(1)
    print(f"{len(tests)} passed")


if __name__ == "__main__":
    main()
