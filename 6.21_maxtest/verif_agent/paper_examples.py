#!/usr/bin/env python3
"""
paper_examples.py — run the agent on the paper's OWN formal-verification examples
(barrier_core.SYSTEMS) using the barriers the pipeline synthesised
(barrier_result_*.json). This is the "does it work on the paper's cases" check,
separate from the core200 dataset sweep.

For exterior-unsafe systems (X_u = complement of the domain), we verify over the
larger X_u_sample_bounds box so Condition 1 (h<0 on X_u) actually sees X_u.
"""
from __future__ import annotations

import os
import sys

_PARENT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from barrier_core import SYSTEMS               # noqa: E402
from verif_agent import verify, route_system   # noqa: E402

# barrier h synthesised by the pipeline (from the barrier_result_*.json files)
PAPER_CERTS = {
    "darboux": "-(1 + 2*x1)*x2**2 - x1**2 + (4/3)*x1**3 - 0.000001",
    "bb_linear": "9 - x1**2 - x2**2",
    "coupled": "4 - x**2 - (17/400)*y**6 - (1/200)*y**8",
    "vanderpol": ("exp(20*((1089/100)*(1 - (25*x**2)/144) - "
                  "(y + (29*x**3)/75 - (2609*x)/1250)**2)) - 1"),
    "ex5": "1 - (x1 - 0.7)**2 - (x2 + 0.7)**2",   # illustrative analytic guess
}


def main():
    print(f"{'system':12} {'class':22} {'chosen':10} {'verdict':9} {'sound':6} {'time':>7}")
    print("-" * 76)
    for key, cert in PAPER_CERTS.items():
        if key not in SYSTEMS:
            continue
        system = dict(SYSTEMS[key])
        system["task_type"] = "barrier"
        system["cert_gt"] = cert
        if system.get("X_u_sample_bounds"):     # verify over the box that contains X_u
            system["X_bounds"] = system["X_u_sample_bounds"]
        routing = route_system(system, cert)
        res = verify(system, cert, timeout_ms=8000)
        print(f"{key:12} {routing['features']:22} {str(res.chosen_backend):10} "
              f"{res.status:9} {str(res.sound):6} {res.elapsed_s:6.2f}s")
        for t in res.trace:
            print(f"      - {t['backend']:9} {t['status']:11} "
                  f"({t['elapsed_s']}s){'  '+str(t.get('detail',{}).get('conditions','')) if t.get('detail',{}).get('conditions') else ''}")


if __name__ == "__main__":
    main()
