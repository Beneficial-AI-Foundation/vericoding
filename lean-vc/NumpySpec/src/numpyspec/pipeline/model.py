from __future__ import annotations

"""Model-driven Lean code generator.

This module consumes docstrings (plus optional Python reference implementations)
and leverages the unified *model* abstraction (`specdraft.models.load_model`) to
produce Lean 4 source code **with accompanying specification comments**.

The generated code is written into a temporary directory so that downstream
steps (e.g. the pipeline *verifier*) can immediately consume it.
"""

from pathlib import Path
import tempfile
from typing import List, Dict, Any

from specdraft.models import load_model

__all__ = [
    "generate_lean_file",
]


_DEFAULT_SYSTEM_PROMPT = (
    "You are a Lean 4 expert.  Translate the following Python/Numpy function "
    "documentation into a Lean module containing:\n"
    "  • A specification comment for each definition (using '/-! ... -/' ).\n"
    "  • Complete Lean implementation(s) that satisfy those specs.\n"
    "Return *only* valid Lean code; do not wrap the output in markdown fences."
)


def _build_user_prompt(doc: str, python_source: str | None = None) -> str:
    """Compose a prompt chunk for a single function/documentation unit."""

    prompt = ["Docstring:\n" + doc.strip()]
    if python_source is not None:
        prompt.append("Python reference implementation:\n" + python_source.strip())
    return "\n\n".join(prompt)


def generate_lean_file(
    docs: str | List[str],
    model_cfg: Dict[str, Any] | None = None,
    *,
    tmp_dir: str | Path | None = None,
) -> Path:
    """Generate Lean source code from *docs* and save it to a temporary file.

    Parameters
    ----------
    docs : str | list[str]
        One or multiple docstrings. When a list is given, they are concatenated
        with separators so the model can generate a module containing all
        definitions.
    model_cfg : dict, optional
        Configuration dictionary as expected by `specdraft.models.load_model`.
        Defaults to a small local GPT-2 model (handy for unit tests – will *not*
        produce meaningful Lean code).
    tmp_dir : str | Path, optional
        Directory to create the temporary `.lean` file in.  If *None*, a fresh
        `tempfile` directory is used.

    Returns
    -------
    Path
        Absolute path to the generated Lean file.
    """

    # ---------------------------------------------------------------------
    # Prepare model
    # ---------------------------------------------------------------------
    if model_cfg is None:
        model_cfg = {
            "type": "local",
            "model_name": "gpt2",
            "generate_kwargs": {"max_new_tokens": 512, "temperature": 0.2},
        }

    generate = load_model(model_cfg)

    # ---------------------------------------------------------------------
    # Build prompts
    # ---------------------------------------------------------------------
    if isinstance(docs, str):
        docs_list = [docs]
    else:
        docs_list = list(docs)

    user_prompts: List[str] = []
    for doc in docs_list:
        user_prompts.append(_build_user_prompt(doc, python_source=None))  # noqa: E501

    # ---------------------------------------------------------------------
    # Run model
    # ---------------------------------------------------------------------
    outputs = generate(_DEFAULT_SYSTEM_PROMPT, user_prompts)

    # Concatenate outputs (might be multiple if docs_list > 1)
    lean_code = "\n\n".join(outputs).strip() + "\n"

    # ---------------------------------------------------------------------
    # Persist to temp file
    # ---------------------------------------------------------------------
    tmp_parent = Path(tmp_dir) if tmp_dir is not None else Path(tempfile.mkdtemp())
    tmp_parent.mkdir(parents=True, exist_ok=True)

    file_path = tmp_parent / "generated.lean"
    file_path.write_text(lean_code, encoding="utf8")

    return file_path 