# Part of the code taken from: https://github.com/ChuyueSun/Clover/blob/main/clover/utils.py
import os
import re
import json
import pandas as pd


helper_functions = "\nfunction abs(a: real) : real {if a>0.0 then a else -a}\n"


def is_doc(line):
    if line.startswith("/*") or line.startswith("//"):
        return True
    return False


def extract_code_from_llm_output(reply):
    i = reply.find("<answer>")
    if i != -1:
        reply = reply[i + 8 :]
        i = reply.find("</answer>")
        reply = reply[:i]
        return reply
    i = reply.find("```dafny")
    if i != -1:
        reply = reply[i + 8 :]
        i = reply.find("```")
        reply = reply[:i]
        return reply
    i = reply.find("```Dafny")
    if i != -1:
        reply = reply[i + 8 :]
        i = reply.find("```")
        reply = reply[:i]
        return reply
    i = reply.find("```")
    if i != -1:
        reply = reply[i + 3 :]
        i = reply.find("```")
        reply = reply[:i]
        return reply
    return reply


def extract_body(lines, oneline=True):
    body = ""
    start = False
    for line in lines:
        if (
            line.strip().startswith("method")
            or line.strip().startswith("returns")
            or line.strip().startswith("function")
        ):
            body += line + "\n"
            continue
        if "include" in line or is_doc(line):
            continue
        if line.strip() == "{":
            start = True
        if not start:
            continue
        if oneline:
            body += line
        else:
            body += line + "\n"
    return body


def dump_tmp_file(program):
    import time

    timestamp = time.time()
    tmp_dir = "tmp"
    os.makedirs(tmp_dir, exist_ok=True)
    tmp_file = f"{tmp_dir}/tmp_dafny_input_{timestamp}.dfy"
    with open(tmp_file, "w") as f:
        f.write(program)
    return tmp_file


def mask_file_names(text):
    file_path_pattern = re.compile(r"\b[\w/_/.]+\.dfy\b")
    masked_text = file_path_pattern.sub("foo.dfy", text)
    return masked_text


def compile_dafny(body, dafny_path, keep_tmp_file=False):
    import subprocess

    program = body + helper_functions

    tmp_file = dump_tmp_file(program)
    try:
        # result = subprocess.run(
        #     f"{dafny_path} /compile:0 /noVerify /deprecation:0  {tmp_file}",
        #     shell=True,
        #     capture_output=True,
        # )

        result = subprocess.run(
            [dafny_path, "compile", tmp_file, "--compile:0", "--noVerify", "--deprecation:0"],
            capture_output=True,
        )

        if os.path.exists(tmp_file) and not keep_tmp_file:
            os.remove(tmp_file) # no need to keep the tmp file if it won't be used again for now


    except Exception as e:
        if os.path.exists(tmp_file) and not keep_tmp_file:
            os.remove(tmp_file)
        return str(e)
    return mask_file_names(str(result.stdout))


def no_compile_error(msg: str):
    return "Dafny program verifier did not attempt verification" in msg


def run_dafny(program, dafny_path, keep_tmp_file=False):
    import subprocess

    tmp_file = dump_tmp_file(program + helper_functions)
    try:
        # s = subprocess.run(
        #     f"{dafny_path} /compile:0  /deprecation:0  {tmp_file}",
        #     shell=True,
        #     capture_output=True,
        #     timeout=15,
        # )
        s = subprocess.run(
            [dafny_path, "verify", tmp_file, "--verification-time-limit", "15"],
            capture_output=True,
        )
        if os.path.exists(tmp_file) and not keep_tmp_file:
            # no need to keep the tmp file if it won't be used again for now
            os.remove(tmp_file)
    except Exception as e:
        return "", str(e)
    return mask_file_names(str(s.stdout)), mask_file_names(str(s.stderr))


def is_dafny_verified(msg: str):
    if "verified, 0 errors" in msg and "File contains no code" not in msg:
        return True
    return False


def check_no_cheating(body, body_reconstructed):
    # Initialize lists to store specification lines (requires/ensures) from both versions
    spec_orig, spec_llm = [], []
    # Track whether we're inside multi-line comments (/* ... */) for both versions
    in_doc, in_doc_hints = False, False

    # Extract specification lines from the original body
    for line in body.split("\n"):
        # Toggle multi-line comment state when encountering /* 
        if line.strip().startswith("/*"):
            in_doc = not in_doc
        # Check if this line is a single-line comment
        is_comment = line.strip().startswith("//")
        # Collect requires/ensures lines that are not in comments or multi-line docs
        if ("requires" in line or "ensures" in line) and (not in_doc) and (not is_comment):
            spec_orig.append(line.strip().replace(" ", ""))
        # Toggle multi-line comment state when encountering */
        if line.strip().endswith("*/"):
            in_doc = not in_doc
    
    # Extract specification lines from the LLM-reconstructed body
    for line_hints in body_reconstructed.split("\n"):
        # Toggle multi-line comment state when encountering /*
        if line_hints.strip().startswith("/*"):
            in_doc_hints = not in_doc_hints
        # Check if this line is a single-line comment
        is_comment_hints = line_hints.strip().startswith("//")
        # Collect requires/ensures lines that are not in comments or multi-line docs
        if ("requires" in line_hints or "ensures" in line_hints) and (not in_doc_hints) and (not is_comment_hints):
            spec_llm.append(line_hints.strip().replace(" ", ""))
        # Toggle multi-line comment state when encountering */
        if line_hints.strip().endswith("*/"):
            in_doc_hints = not in_doc_hints
    
    # Check if the specifications are preserved (same requires/ensures clauses)
    spec_preserved = spec_orig == spec_llm
    # Check that the LLM didn't use verification-disabling tricks
    no_avoid_verify = not '{:verify false}' in body_reconstructed and not 'assume false' in body_reconstructed
    return spec_preserved, no_avoid_verify


def save_result_stats(model, test_file, success_attempt):
    results_file = f"../results/results_summary/{model}_results.csv"
    df = pd.read_csv(results_file)
    new_test_result = {"test_ID": get_test_ID(test_file), "test_file": test_file, "success_on_attempt_#": success_attempt}
    df = df._append(new_test_result, ignore_index=True)
    df["test_ID"] = df["test_ID"].apply(lambda x: f"{int(x):03d}")
    df.to_csv(results_file, index=False)

def check_already_saved(model, test_file):
    results_file = f"../results/results_summary/{model}_results.csv"
    df = pd.read_csv(results_file)
    test_ID = get_test_ID(test_file)
    if test_ID in df["test_ID"].values or test_file in df["test_file"].values:
        if df[df["test_file"] == test_file]["success_on_attempt_#"].values[0] == "failed api":
            return False
        else:
            return True
    return False

def save_reconstructed_file(model, test_file, body_reconstructed):
    output_file = f"../results/reconstructed_files/{model}_outputs.json"
    test_ID = get_test_ID(test_file)
    new_test_result = {"test_ID": test_ID, "test_file": test_file, "llm_output": body_reconstructed}

    os.makedirs(os.path.dirname(output_file), exist_ok=True)
    if os.path.exists(output_file):
        with open(output_file, "r") as f:
            try:
                data = json.load(f)
                if not isinstance(data, dict):
                    data = {}
            except json.JSONDecodeError:
                data = {}
    else:
        data = {}
    
    with open(output_file, "r") as f:
        data = json.load(f)
    
    data[test_ID] = new_test_result

    with open(output_file, "w") as f:
        json.dump(data, f, indent=4)


def save_result(model, test_file, success_attempt, body_reconstructed):
    save_result_stats(model, test_file, success_attempt)
    save_reconstructed_file(model, test_file, body_reconstructed)


def get_test_ID(test_file):
    metadata_file = "../DafnyBench/metadata/hints_removed_metadata.csv"
    df = pd.read_csv(metadata_file)
    test_ID = df[df["test_file"] == test_file]["test_ID"].values[0]
    return f"{test_ID:03d}"
