#!/usr/bin/env python3
"""The versions of the published packages (ADR 0044).

    scripts/versions.py check       the five packages have the same version,
                                    and the ranges between them contain it
    scripts/versions.py tag TAG     the cabal version that TAG releases
                                    (v0.1.0 and v0.1.0-rc1 give 0.1.0), and
                                    fail unless the packages have it
    scripts/versions.py self-test   the examples of the functions below
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PACKAGES = ["peg-runtime", "peg-grammar", "peg-codegen", "peg-lsp", "peg-cli"]


def parse_version(s):
    return tuple(int(x) for x in s.split("."))


def tag_version(tag):
    """The first three components of the cabal version that a tag releases.
    The part after '-' marks a pre-release (v0.1.0-rc1), which has the cabal
    version of the release: PVP versions cannot say rc."""
    m = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)(-[0-9A-Za-z.]+)?", tag)
    if not m:
        raise ValueError(f"not a release tag: {tag} (expected vA.B.C or vA.B.C-SUFFIX)")
    return tuple(int(m.group(i)) for i in (1, 2, 3))


def is_prerelease(tag):
    tag_version(tag)
    return "-" in tag


def package_version(text):
    m = re.search(r"^version:\s*(\S+)\s*$", text, re.M)
    if not m:
        raise ValueError("no version field")
    return parse_version(m.group(1))


def dependency_ranges(text):
    """The ranges of the dependencies on the packages of this repository, as
    (name, lower, upper) from the form 'peg-x >=A && <B'."""
    return [
        (name, parse_version(lo), parse_version(hi))
        for name, lo, hi in re.findall(
            r"\b(peg-(?:runtime|grammar|codegen|lsp))\s+>=\s*([\d.]+)\s*&&\s*<\s*([\d.]+)", text
        )
    ]


def in_range(v, lo, hi):
    return lo <= v < hi


def problems(cabals):
    """The problems of the versions of the packages, given as {name: text}."""
    versions = {name: package_version(text) for name, text in cabals.items()}
    out = []
    if len(set(versions.values())) > 1:
        listed = ", ".join(f"{n} {'.'.join(map(str, v))}" for n, v in versions.items())
        out.append(f"the packages have different versions: {listed}")
    for name, text in cabals.items():
        for dep, lo, hi in dependency_ranges(text):
            v = versions.get(dep)
            if v is not None and not in_range(v, lo, hi):
                out.append(
                    f"{name}: the range of {dep} (>={'.'.join(map(str, lo))} && <{'.'.join(map(str, hi))})"
                    f" does not contain its version {'.'.join(map(str, v))}"
                )
    return out


def read_cabals():
    return {p: (ROOT / "packages" / p / f"{p}.cabal").read_text(encoding="utf-8") for p in PACKAGES}


def self_test():
    assert tag_version("v0.1.0") == (0, 1, 0)
    assert tag_version("v0.1.0-rc1") == (0, 1, 0)
    assert tag_version("v12.3.45") == (12, 3, 45)
    for bad in ["0.1.0", "v0.1", "v0.1.0.0", "v0.1.0-", "release", "v0.1.0 "]:
        try:
            tag_version(bad)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted {bad!r}")
    assert is_prerelease("v0.1.0-rc1") and not is_prerelease("v0.1.0")
    one = "version: 0.1.0.0\nbuild-depends:\n    , peg-runtime  >=0.1  && <0.2\n"
    assert package_version(one) == (0, 1, 0, 0)
    assert dependency_ranges(one) == [("peg-runtime", (0, 1), (0, 2))]
    good = {"peg-runtime": "version: 0.1.0.0\n", "peg-grammar": one}
    assert problems(good) == []
    differ = {"peg-runtime": "version: 0.2.0.0\n", "peg-grammar": one}
    assert len(problems(differ)) == 2  # the versions, and the range of peg-runtime
    narrow = {"peg-runtime": "version: 0.1.0.0\n", "peg-grammar": one.replace("<0.2", "<0.1.0.0")}
    assert len(problems(narrow)) == 1
    print("self-test: ok")


def main(args):
    if args == ["self-test"]:
        self_test()
        return 0
    cabals = read_cabals()
    errors = problems(cabals)
    if args == ["check"]:
        pass
    elif len(args) == 2 and args[0] == "tag":
        try:
            want = tag_version(args[1])
        except ValueError as e:
            errors.append(str(e))
        else:
            for name, text in cabals.items():
                have = package_version(text)
                if have[:3] != want:
                    errors.append(
                        f"the tag {args[1]} releases {'.'.join(map(str, want))}, but {name} has the version "
                        f"{'.'.join(map(str, have))}"
                    )
    else:
        print(__doc__, file=sys.stderr)
        return 2
    for e in errors:
        print(f"versions.py: {e}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
