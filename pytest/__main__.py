import traceback
from test_compile import (
    test_canonical_proof_guards,
    test_global_floor_certificate,
    test_main_tex_compiles_cleanly,
    test_source_profile_symbolic_certificate,
)


def main():
    tests = (
        test_global_floor_certificate,
        test_source_profile_symbolic_certificate,
        test_canonical_proof_guards,
        test_main_tex_compiles_cleanly,
    )
    for test in tests:
        try:
            test()
        except Exception:
            traceback.print_exc()
            raise SystemExit(1)
    print(f"{len(tests)} passed")


if __name__ == "__main__":
    main()
