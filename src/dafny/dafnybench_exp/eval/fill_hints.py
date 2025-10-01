import argparse
import sglang as sgl
from sglang import OpenAI, Anthropic, VertexAI, Runtime, assistant, gen, set_default_backend, system, user
import os
import logging
from llm_providers import OpenRouterProvider
from sys_prompts import SYS_DAFNY, GEN_HINTS_FROM_BODY
from utils import (
    extract_code_from_llm_output,
    run_dafny,
    is_dafny_verified,
    check_no_cheating,
    save_result,
    check_already_saved,
    get_test_ID,
)


# Function adapted from: https://github.com/ChuyueSun/Clover/blob/main/clover/clover.py
@sgl.function
def fill_hints_sglang(s, model, test_file, dafny_path, feedback_turn, temperature=0.3):
    program_path = f"../DafnyBench/dataset/hints_removed/{test_file}"
    if check_already_saved(model, test_file):
        return True

    with open(program_path, "r") as file:
        body = file.read()
    
    s += system(SYS_DAFNY)
    s += user(GEN_HINTS_FROM_BODY + body)
    body_with_hints = ""
    counter = 1

    # Give LLM multiple tries to reconstruct hints (& take into account Dafny feedback)
    for _ in range(feedback_turn):
        with s.copy() as tmp:
            tmp += assistant(gen("new_body_with_hints", max_tokens=4096, temperature=0.3))
            body_with_hints = extract_code_from_llm_output(tmp["new_body_with_hints"])
        s += assistant(body_with_hints)
        out, _ = run_dafny(body_with_hints, dafny_path, keep_tmp_file=False)
        spec_preserved, no_avoid_verify = check_no_cheating(body, body_with_hints)

        if is_dafny_verified(str(out)) and spec_preserved and no_avoid_verify:
            save_result(model, test_file, counter, body_with_hints)
            return True
        
        with s.user():
            if not is_dafny_verified(str(out)):
                s += "This answer got Dafny verification error:\n" + str(out) + "\n"
                s += "Please try again by taking the Dafny feedback.\n"
            if not spec_preserved:
                s += "Please keep the preconditions and postconditions the same as the original program, or you fail the test.\n"
            if not no_avoid_verify:
                s += "Please don't use {:verify false} or assume false."
            counter += 1
    
    save_result(model, test_file, "failed", body_with_hints)
    return False

def fill_hints_llm_providers(model, test_file, dafny_path, feedback_turn, temperature=0.3, api_attempts_per_turn=3):
    program_path = f"../DafnyBench/dataset/hints_removed/{test_file}"
    if check_already_saved(model, test_file):
        logging.info(f"Model {model} has already saved results for test file {test_file}")
        return True

    with open(program_path, "r") as file:
        body = file.read()

    system_prompt = SYS_DAFNY
    user_prompt = GEN_HINTS_FROM_BODY + body

    body_with_hints = ""
    counter = 1

    max_tokens = 4096*2
    timeout = 120

    if model.startswith("gpt"):
        openrouter_provider = OpenRouterProvider(os.getenv("OPENROUTER_API_KEY"), "openai/" + model, max_tokens=max_tokens, timeout = timeout)
    elif model.startswith("claude"):
        openrouter_provider = OpenRouterProvider(os.getenv("OPENROUTER_API_KEY"), "anthropic/" + model, max_tokens=max_tokens, timeout = timeout)
    elif model.startswith("gemini"):
        openrouter_provider = OpenRouterProvider(os.getenv("OPENROUTER_API_KEY"), "google/" + model, max_tokens=max_tokens, timeout = timeout)
    elif model.startswith("grok"):
        openrouter_provider = OpenRouterProvider(os.getenv("OPENROUTER_API_KEY"), "x-ai/" + model, max_tokens=max_tokens, timeout = timeout)
    elif model.startswith("glm"):
        openrouter_provider = OpenRouterProvider(os.getenv("OPENROUTER_API_KEY"), "z-ai/" + model, max_tokens=max_tokens, timeout = timeout)
    elif model.startswith("deepseek"):
        openrouter_provider = OpenRouterProvider(os.getenv("OPENROUTER_API_KEY"), "deepseek/" + model, max_tokens=max_tokens, timeout = timeout)
    else:
        raise ValueError("Unsupported model company")
    # Give LLM multiple tries to reconstruct hints (& take into account Dafny feedback)
    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_prompt},
    ]
    for _ in range(feedback_turn):
        logging.info("\t On attempt " + str(counter))
        api_success = False
        for i in range(api_attempts_per_turn):
            try:
                response = openrouter_provider.call_api(messages, temperature=temperature, max_tokens=max_tokens)
                api_success = True
                break
            except Exception as e:
                logging.info(f"Error calling OpenRouter API: {e}")
                # # Add 4096 tokens to max_tokens
                # max_tokens = max_tokens + 4096
        if not api_success:
            logging.info(f"All {api_attempts_per_turn} API attempts failed for attempt {counter}")
            save_result(model, test_file, "failed api", body_with_hints)
            return False

        logging.info("\t Got response from OpenRouter")

        body_with_hints = extract_code_from_llm_output(response.text)
        messages.append({"role": "assistant", "content": body_with_hints})
        out, _ = run_dafny(body_with_hints, dafny_path)
        logging.info("\t Dafny verification result: " + str(out))
        logging.info("\t Dafny verification error: " + str(_))

        spec_preserved, no_avoid_verify = check_no_cheating(body, body_with_hints)
        if is_dafny_verified(str(out)) and spec_preserved and no_avoid_verify:
            save_result(model, test_file, counter, body_with_hints)
            logging.info("\t Model satisfies spec and is verified\n")
            return True

        logging.info("\t Model does not satisfy spec or is not verified\n")
        next_user_prompt = ""
        if not is_dafny_verified(str(out)):
            next_user_prompt += "\nThis answer got Dafny verification error:\n" + str(out) + "\n"
            next_user_prompt += "Please try again by taking the Dafny feedback.\n"
        if not spec_preserved:
            next_user_prompt += "Please keep the preconditions and postconditions the same as the original program, or you fail the test.\n"
        if not no_avoid_verify:
            next_user_prompt += "Please don't use {:verify false} or assume false."
        messages.append({"role": "user", "content": next_user_prompt})
        counter += 1

    save_result(model, test_file, "failed", body_with_hints)
    return False


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Reconstruct hints for a Dafny program")
    parser.add_argument("--model", type=str, required=True)
    parser.add_argument("--test_file", type=str, required=True)
    parser.add_argument("--feedback_turn", type=int, default=10, help="# of feedback turns to give the LLM")
    parser.add_argument("--dafny_path", type=str, required=True, help="Path to the Dafny executable")
    parser.add_argument("--temperature", type=float, default=0.3, help="Temperature for the LLM")
    parser.add_argument("--llm_providers", type=str, default="sglang", help="LLM provider to use")
    parser.add_argument("--log_file", type=str, help="Path to log file")

    args = parser.parse_args()

    # Set up logging
    if args.log_file:
        logging.basicConfig(
            level=logging.INFO,
            format='[%(asctime)s] %(message)s',
            handlers=[
                logging.FileHandler(args.log_file, mode='a'),
                logging.StreamHandler()  # Also print to stdout
            ]
        )
    else:
        logging.basicConfig(level=logging.INFO)
    test_ID = get_test_ID(args.test_file)
    logging.info(f"Running eval with model: {args.model} on test_file_ID: {test_ID}")
    if args.llm_providers == "sglang":
        # Model name examples: gpt-4o, gpt-4-turbo, gpt-3.5-turbo, claude-3-opus-20240229, gemini-1.5-pro-preview-0409, etc.
        if args.model.startswith("gpt"):
            set_default_backend(OpenAI(args.model))
        elif args.model.startswith("claude"):
            set_default_backend(Anthropic('claude-3-opus-20240229'))
        elif args.model.startswith("gemini"):
            set_default_backend(VertexAI(args.model))
        elif args.model.startswith("codellama-7b"):
            runtime = Runtime(model_path="codellama/CodeLlama-7b-Instruct-hf")
            set_default_backend(runtime)
        else:
            raise ValueError("Invalid model name")

        # Reconstruct hints, check if the program verifies
        print(f"Filling hints with {args.model} using SGLang")
        verified = fill_hints_sglang(args.model, args.test_file, args.dafny_path, args.feedback_turn, args.temperature)

    elif args.llm_providers == "openrouter":
        print(f"Filling hints with {args.model} using OpenRouter")
        verified = fill_hints_llm_providers(args.model, args.test_file, args.dafny_path, args.feedback_turn, args.temperature)
    