# D3 Lean classroom files

These files import Mathlib and must be opened or compiled from a configured
Mathlib Lake project. The D3 distribution folder is not itself a Lake project:
it does not contain `lakefile.lean` or `lean-toolchain`.

From an existing Mathlib project, run a file with:

```sh
cd /path/to/mathlib-project
lake env lean /path/to/D3/D3_01_Inspect.lean
```

In VS Code, open the configured Lake project as the workspace, then open the D3
files from that session. Keep the PDF and Lean files in the same folder so the
relative `Live Lean` links continue to target the corresponding source files.
