# SPDX-License-Identifier: GPL-3.0-or-later
"""Command line interface::

    python -m cubic_twostage cover "x^2 - 14" [-o cert.pkl] [--Nmax 100]
    python -m cubic_twostage cf "x^3 - x^2 - 2*x - 3" "(2 + 3*t + 5*t^2)/(7 - t)" [-c cert.pkl]
    python -m cubic_twostage verify [certificate_dir] [--shard i/n]

(also installed as the command ``cubic-twostage``).  Field elements are written in the
generator ``t`` of the field defined by the polynomial.
"""

import argparse
import sys


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv[:1] == ["verify"]:
        from .verify import main as vmain

        return 0 if vmain(argv[1:]) else 1
    p = argparse.ArgumentParser(
        prog="cubic-twostage", description=__doc__.split("::")[0]
    )
    sub = p.add_subparsers(dest="cmd", required=True)
    pc = sub.add_parser("cover", help="find and certify a covering, print its level N")
    pc.add_argument("poly")
    pc.add_argument("-o", "--output", help="save the certificate (pickle) here")
    pc.add_argument("--Nmax", type=int, default=100)
    pc.add_argument("-v", "--verbose", action="store_true")
    pf = sub.add_parser("cf", help="continued fraction of an element")
    pf.add_argument("poly")
    pf.add_argument("x", help="element, in terms of the generator t")
    pf.add_argument(
        "-c", "--certificate", help="use this certificate instead of searching"
    )
    sub.add_parser("verify", help="verify the certificates cert_*.pkl in a directory")
    a = p.parse_args(argv)

    from sage.all import QQ, PolynomialRing, sage_eval

    from .twostage import TwoStage, evaluate_cf

    try:
        if a.cmd == "cover":
            S = TwoStage(a.poly)
            N = S.find_covering(Nmax=a.Nmax, verbose=a.verbose)
            print(
                f"{S.K}: covering of level N = {N} with {len(S.cert)} boxes (certified)"
            )
            if a.output:
                S.save_certificate(a.output)
                print("certificate saved to", a.output)
        elif a.cmd == "cf":
            if a.certificate:
                S = TwoStage.from_certificate(a.certificate)
                f = PolynomialRing(QQ, "x")(a.poly)
                if f.list() != S.K.defining_polynomial().list():
                    p.error(f"the certificate is for {S.K.defining_polynomial()}")
            else:
                S = TwoStage(a.poly)
            x = S.K(sage_eval(a.x, locals={"t": S.K.gen()}))
            qs = S.continued_fraction(x)
            assert evaluate_cf(qs) == x
            print(qs)
    except ValueError as e:
        p.exit(1, f"cubic-twostage: error: {e}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
