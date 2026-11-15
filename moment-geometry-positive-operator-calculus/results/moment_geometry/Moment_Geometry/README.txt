COMPUTATIONAL SUPPLEMENTS

Companion to Moment geometry and positive operator calculus.

Read supplements/README.txt for the reusable interfaces and arithmetic scope.
The included formalization.pdf is the 12-page theorem and dependency guide.

From this directory, create an environment and install the requirements:
  python3 -m venv .venv
  .venv/bin/python -m pip install -r supplements/requirements.txt
  .venv/bin/python supplements/verify_all.py --include-diagnostics

The included run passed all 25 suites: 18 exact, 3 certified-arithmetic,
and 4 bounded floating-point diagnostics. Monte Carlo was disabled.
Do not use Python -O or -OO for verification scripts.

The theorem registry refers to article proof files by paths in the complete
or TeX/source distribution. Those proof files are intentionally not duplicated
in this smaller computational archive. All executable dependencies are here.
The full article and the complete TeX/source archive are separate downloads.
No complete proof-assistant verification of the article is claimed.
