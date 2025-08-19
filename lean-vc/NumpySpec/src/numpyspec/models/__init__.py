from __future__ import annotations

"""SpecDraft – generic model loading & generation utilities.

This module offers a unified interface that turns a *model configuration* dictionary
into a *generator function* that can be called with

    outputs = generate(system_prompt: str, user_prompts: list[str]) -> list[str]

Two backend implementations are supported:

1. **Local model** – Loads a HuggingFace model ( `transformers` ) on the current machine.
   The configuration must contain at least::

       {"type": "local", "model_name": "<hf-repo-or-path>"}

   Optional keys:
       • device          – "cuda", "cpu", or an int specifying the GPU id (default: auto)
       • generate_kwargs – dict forwarded to `model.generate` (e.g. max_new_tokens)
       • prompt_template – Either a string with two placeholders ``{system}`` and ``{user}``,
                           or ``None`` (default: "{system}\n{user}")

2. **API model** – Sends HTTP requests to a remote endpoint that performs inference.
   The configuration must contain at least::

       {"type": "api", "url": "https://…"}

   Optional keys:
       • headers         – HTTP headers to add (e.g. authorisation)
       • timeout         – Seconds for the request timeout (default: 30)
       • retries         – How many times to retry transient failures (default: 3)
       • prompt_template – same semantics as for local model.

The generated callable intentionally remains very thin – it only performs prompt
formatting, model invocation, and decoding.  Advanced logic such as accelerated
batched generation can be layered on top later without changing the public API.
"""

from typing import Callable, List, Dict, Any, Optional
import logging
import time

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Helper – prompt formatting
# ---------------------------------------------------------------------------

def _format_prompt(system_prompt: str, user_prompt: str, template: Optional[str] = None) -> str:
    """Fill the user+system prompts into *template*.

    If *template* is ``None`` we fall back to a minimal "{system}\n{user}".
    """

    if template is None:
        template = "{system}\n{user}"
    try:
        return template.format(system=system_prompt, user=user_prompt)
    except KeyError as exc:
        raise ValueError(f"`prompt_template` must contain {{system}} and {{user}} placeholders – missing: {exc}") from exc

# ---------------------------------------------------------------------------
# Local – HuggingFace transformers
# ---------------------------------------------------------------------------

class _LocalModel:
    def __init__(self, cfg: Dict[str, Any]):
        try:
            from transformers import (  # pylint: disable=import-error
                AutoModelForCausalLM,
                AutoTokenizer,
            )
        except ImportError as exc:
            raise ImportError(
                "`transformers` is required for local models; please `pip install transformers`"
            ) from exc

        model_name = cfg.get("model_name") or cfg.get("model_name_or_path")
        if not model_name:
            raise ValueError("Local model config must specify 'model_name'.")

        device = cfg.get("device")
        if device is None:
            # Auto-detect GPU if available; otherwise CPU.
            try:
                import torch  # pylint: disable=import-error

                device = "cuda" if torch.cuda.is_available() else "cpu"
            except ImportError:
                device = "cpu"

        logger.info("Loading local model '%s' onto %s …", model_name, device)

        self.tokenizer = AutoTokenizer.from_pretrained(model_name)
        # ensure padding token to avoid warnings; many causal models lack it.
        if self.tokenizer.pad_token is None:
            self.tokenizer.pad_token = self.tokenizer.eos_token

        self.model = AutoModelForCausalLM.from_pretrained(model_name)
        # `.to` is NO-OP for CPU strings like "cpu"; fine.
        self.model.to(device)

        self.device = device
        self.generate_kwargs = cfg.get("generate_kwargs", {})
        # get template from model, if not, try to find it in the model config
        self.prompt_template = cfg.get("prompt_template")
        if self.prompt_template is None:
            self.prompt_template = self.model.config.prompt_template

    # .....................................................................

    def generate(self, system_prompt: str, user_prompts: List[str]) -> List[str]:
        """Generate a response for each *user_prompt*.

        Returns *len(user_prompts)* strings in the same order.
        """

        import torch  # pylint: disable=import-error

        prompts = [
            _format_prompt(system_prompt, up, self.prompt_template)
            for up in user_prompts
        ]

        logger.debug("Prompts fed into local model: %s", prompts)

        inputs = self.tokenizer(prompts, return_tensors="pt", padding=True).to(self.device)

        with torch.no_grad():
            output_ids = self.model.generate(
                **inputs,
                **{
                    "max_new_tokens": 128,
                    "do_sample": True,
                    "temperature": 0.7,
                    **self.generate_kwargs,
                },
            )

        # We only want the newly generated tokens, not the prompt part.
        results = []
        for prompt, out in zip(prompts, output_ids):
            decoded = self.tokenizer.decode(out, skip_special_tokens=True)
            # hew off the original prompt prefix to keep only the answer.
            # This is heuristic – but works for standard causal models.
            if decoded.startswith(prompt):
                decoded = decoded[len(prompt) :]
            results.append(decoded.strip())
        return results

# ---------------------------------------------------------------------------
# Remote – generic HTTP API
# ---------------------------------------------------------------------------

class _APIModel:
    def __init__(self, cfg: Dict[str, Any]):
        import requests  # local import to avoid mandatory dependency for local-only users.

        url = cfg.get("url") or cfg.get("endpoint")
        if not url:
            raise ValueError("API model config must specify 'url'.")

        self.url = url
        self.headers = cfg.get("headers", {})
        self.timeout = cfg.get("timeout", 30)
        self.retries = cfg.get("retries", 3)
        self.prompt_template = cfg.get("prompt_template")
        # Optional static fields to include in every request (e.g. {"model": "gpt-4o"})
        self.base_payload: Dict[str, Any] = cfg.get("base_payload", {})

        # We keep session to persist TCP connection and cookies.
        self._session = requests.Session()
        self._session.headers.update(self.headers)

    # .....................................................................

    def _post_json(self, payload: dict) -> dict:
        import requests

        for attempt in range(1, self.retries + 1):
            try:
                response = self._session.post(self.url, json=payload, timeout=self.timeout)
                response.raise_for_status()
                return response.json()
            except requests.RequestException as exc:
                logger.warning("API request failed (attempt %d/%d): %s", attempt, self.retries, exc)
                if attempt == self.retries:
                    raise
                # Exponential back-off: 1s, 2s, 4s …
                time.sleep(2 ** (attempt - 1))
        # Should never reach here
        raise RuntimeError("Unreachable code after retries loop")

    # .....................................................................

    def generate(self, system_prompt: str, user_prompts: List[str]) -> List[str]:
        outputs: List[str] = []
        for up in user_prompts:
            prompt = _format_prompt(system_prompt, up, self.prompt_template)
            payload = {
                "prompt": prompt,
            }
            # Merge user-specified static values (model name, parameters, etc.)
            payload.update(self.base_payload)
            logger.debug("Sending payload to API: %s", payload)
            result = self._post_json(payload)
            # Accept diverse response formats:
            #   • {"text": "…"}
            #   • {"choices": [{"text": "…"}, …]}
            #   • {"choices": [{"message": {"content": "…"}}, …]}
            if "text" in result:
                outputs.append(result["text"].strip())
            elif "choices" in result and result["choices"]:
                choice0 = result["choices"][0]
                if isinstance(choice0, dict):
                    if "text" in choice0:
                        outputs.append(choice0["text"].strip())
                    else:
                        outputs.append(choice0.get("message", {}).get("content", "").strip())
                else:
                    # choices may be plain strings in some APIs
                    outputs.append(str(choice0).strip())
            else:
                raise ValueError(f"Unexpected API response format: {result}")
        return outputs

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def load_model(cfg: Dict[str, Any]) -> Callable[[str, List[str]], List[str]]:
    """Factory that turns *cfg* into a *generate* callable.

    Example::

        cfg = {"type": "local", "model_name": "gpt2"}
        generate = load_model(cfg)
        answers = generate("You are a helpful assistant.", ["Hello", "How are you?"])
    """

    mtype = cfg.get("type", "local").lower()
    if mtype == "local":
        backend = _LocalModel(cfg)
    elif mtype == "api":
        backend = _APIModel(cfg)
    else:
        raise ValueError(f"Unknown model type '{mtype}'. Use 'local' or 'api'.")

    return backend.generate

__all__ = ["load_model"] 