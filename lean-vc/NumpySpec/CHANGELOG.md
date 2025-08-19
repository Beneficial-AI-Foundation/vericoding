# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2025-04-14

### Added

- Initial project structure with `lakefile.toml`, `Main.lean`, and `GaussianSpec.lean`.
- `mathlib` dependency.
- Specification `gaussianElimination_is_left_inverse` stating Gaussian elimination yields a left inverse.
- Placeholder `gaussianElimination` function.
- Imported `LeanSearchClient` in `Main.lean`.

### Changed

- Updated `lean-toolchain` to `leanprover/lean4:v4.19.0-rc3` for `mathlib` compatibility.
- Refined `lakefile.toml` configuration.

### Removed

- Default `IO.println` in `Main.lean`.

## [0.0.1] - 2024-07-19

### Added

- Initial README.md, CHANGELOG.md, LICENSE, .gitignore, lean-toolchain.

## [0.2.0] - 2025-04-15

### Added
- MorphCloud-driven Lean agent in `src/gaussianspec/agent.py` for compositional feedback loop:
  - Drives Lean code edits, builds, and parses feedback.
  - Uses morphcloud SDK (ready for orchestration).
  - Pure functional idioms, data-oriented design, type signatures.
  - Example usage for future MorphCloud integration.

## [0.2.1] - 2025-04-15

### Added
- Pure functional OCR preprocessing step to agent pipeline:
  - Uses pdf2image and pytesseract to OCR textbook PDF.
  - Caches OCR result as .txt file, skipping if already present.
  - Composable and documented; integrated as preproc in agent pipeline.

## [0.3.0] - 2025-04-15

### Added
- Modular subagent classes in `src/gaussianspec/subagents.py`:
  - `OCRSubagent`, `LeanEditSubagent`, `LeanBuildSubagent`, `FeedbackParseSubagent`.
  - Each is a pure dataclass with a `run()` method and clear feedback/result type.
  - Enables compositional, forkable, feedback-driven agent pipelines.
- Updated dependencies (`uv.lock`, `pyproject.toml`) for subagent support.

## [0.4.0] - 2025-05-01

### Added
- Reinforcement‑learning scaffolding (`LeanEnv`, `EditLibrary`) in `src/gaussianspec/rl_env.py`.
  Provides Gymnasium‑compatible environment exposing Lean build feedback.
- Exported in package root for easy import `from gaussianspec import LeanEnv`.
- Added dependencies: `pantograph>=0.3.0` (Lean REPL orchestration) and `gymnasium>=0.29.1`.

## [0.4.1] - 2025-05-20

### Added

- Multi‑backend OCR with automatic fallback in `agent.py`:
  - New `auto` mode tries **OpenAI Vision (GPT‑4o‑mini) → Google Gemini → local Tesseract**.
  - Copyright / policy refusal detection falls back to next provider.
  - `pdf_pipeline` CLI exposes `--method auto|openai|gemini|tesseract` (default `auto`).
  - Helper functions `_openai_ocr_images`, `_ocr_refused`.

### Changed

- Added `openai>=1.30.0` dependency in `pyproject.toml`.

### Fixed

- Type‑checker false positive for `txt_path.write_text` by asserting text not‑None.

## [Unreleased]

- Added runtime guard for optional local Tesseract backend in `agent.py`, removing unconditional `pytesseract` import to fix linter when dependency is absent.

- **Breaking** `ocr_pdf_to_text` now accepts a `strip_right_px` argument that crops a fixed
  number of pixels from the right margin before OCR.  CLI `pdf_pipeline` exposes
  `--strip-right` flag.  Useful for textbooks like *Numerical Recipes* whose sample
  page column interferes with OCR accuracy.

### Added

- Added `external/morphcloud-examples-public` git worktree/submodule pointing to
  `https://github.com/morph-labs/morphcloud-examples-public` to serve as new
  Pantograph example basis and provide LLM context.

### Changed

- Bumped `morphcloud` dependency to `>=0.1.67` in `pyproject.toml`.

## [0.4.2] - PLACEHOLDER_DATE

### Added

- Verbose, batched OCR with `tqdm` progress bar in `agent.py`.
- Parallel page-level OCR using `ThreadPoolExecutor` with `as_completed` preserving page order.
- Added `tqdm>=4.66.4` dependency to `pyproject.toml`.

### Changed

- `ocr_pdf_to_text` now shows a live progress bar and can process pages concurrently even when using non-Tesseract providers (which release the GIL internally).

## [0.4.3] - 2025-04-26

### Added
- Ignored `.env` and `.env.*` files in `.gitignore` with an exception for `.env.example` to keep a template in version control.

## [0.4.4] - 2025-04-26

### Added
- `.gitignore` updated to ignore environment files (`.env`, `.env.*`) while keeping `.env.example`.

### Security
- Credentials are now loaded from local `.env` and mirrored to GitHub Secrets via `gh secret set`.

## [0.4.5] - 2025-04-26

### Added
- CI workflow now exposes secret API keys via `env:`.
- Package auto-loads `.env` at import time when `python-dotenv` is available.
- Added `python-dotenv` to dependencies.

## [0.5.0] - 2025-04-24

### Added
- Introduced `generated/versobook` sub-project for Verso-based documentation.
  - New `LakeProjectInitSubagent` in `subagents.py` provides idempotent project creation with Verso dependency.
  - Driver script `src/gaussianspec/build_book_agents.py` populates a stub `Book/Chapter2.lean` from OCR text.
- Extended Justfile with `build-book` and `refresh-book` targets to compile and regenerate the Verso book.

### Changed

- Updated `lean-toolchain` to `leanprover/lean4:nightly-2025-04-23` to align with Verso nightly requirement.

### Added

- **Remote Lean build**: new `LeanRemoteBuildSubagent` in `gaussianspec.subagents` compiles Lean code via a Pantograph Lean server provisioned on Morph Cloud.  Uses infrastructure from `external/morphcloud-examples-public/lean-server` and wraps provisioning logic in `gaussianspec.lean_server`.
- `pipeline.py` gains `--remote` flag to switch build stage from local `lake build` to remote Pantograph compilation.
  Example:
  ```bash
  uv run -m gaussianspec.pipeline --pdf textbook/Numerical_Recipes_in_C.pdf \
      --lean-file GaussianSpec.lean \
      --remote --edit "theorem t : 1 = 1 := by rfl"
  ```

### Changed

- `subagents.py` now imports `asyncio`, `gaussianspec.lean_server`.

## [0.5.1] - 2025-04-28:23:55 UTC

### Added

- `pdf_pipeline.py` now **reuses the shared `PDFCropSubagent`** so that OCR is
  performed on the *cropped* PDF rather than the original source.  The
  subagent is executed once per run and is idempotent.
- Updated `pipeline.md` with a **mermaid diagram** of the OCR preprocessor flow
  showing the new cropping stage.

### Fixed

- CLI output of `pdf_pipeline` now clearly indicates when cropping fails and
  falls back to the original PDF, aiding debugging.

## [0.6.0] - 2025-04-30:18:32 UTC

### Removed

- Dropped `verso` dependency from `lakefile.toml` due to incompatibility with latest `mathlib4`.
- Commented out `LeanSearchClient` import in `Main.lean` until feature gating reintroduced.

### Changed

- Regenerated `lake-manifest.json` via `lake update`.
- Rebuilt project successfully with only `mathlib`.

## [0.6.1] - 2025-05-15:07:23 UTC

### Changed

- Removed `scripts/install_leantool.py`, `scripts/ensure_pantograph_wheel.py` and the `.wheels` directory. Dependency flow is now fully declarative.
- Simplified `Justfile` `sync` target to a single `uv sync` command.
- Bumped Pantograph to `>=0.3.1` and introduced LeanTool via git tag `v0.3.0+packaging-fix` in `pyproject.toml`.

### Added

- Documentation updates in README to reflect simplified installation.

## [0.7.0] - 2025-06-20

### Changed

- **Project renamed** from GaussianSpec to NumpySpec to reflect focus on numpy-compatible operations
- All references to Gaussian elimination removed in favor of general matrix operations
- Main Lean module renamed from `GaussianSpec.lean` to `NumpySpec.lean`
- Python package renamed from `gaussianspec` to `numpyspec`
- Repository URL updated to `https://github.com/Beneficial-AI-Foundation/NumpySpec`

### Added

- New numpy-focused matrix operations: `Matrix.add`, `Matrix.multiply`, `Matrix.transpose`
- Comprehensive README rewrite emphasizing formal verification and numpy compatibility
- Updated install script (now `.github/scripts/setup.sh`) for CI and OpenAI Codex Universal integration
- Numpy port roadmap with verification strategy

### Removed

- Old `GaussianSpec/` subdirectory and Gaussian elimination focus
- Obsolete install scripts (`install.sh`, `setup_codex.sh`)
- References to textbook OCR and verso documentation system
