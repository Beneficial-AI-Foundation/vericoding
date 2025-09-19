#!/usr/bin/env python3
"""
Script to check if all executable functions in Verus YAML files contain only Rust native types.
This validates that no mathematical types like Seq<>, int, nat are used in executable function signatures.
"""

import re
import yaml
import argparse
from pathlib import Path
from typing import List, Tuple
from dataclasses import dataclass


@dataclass
class TypeIssue:
    file_path: str
    function_name: str
    issue_type: str
    line_number: int
    line_content: str
    suggestion: str


class VerusTypeChecker:
    def __init__(self):
        # Mathematical types that should NOT appear in executable functions
        self.forbidden_types = {
            "Seq<int>",
            "Seq<nat>",
            "Seq<u32>",
            "Seq<i32>",
            "Seq<u8>",
            "Seq<i8>",
            "int",
            "nat",
            # Nested sequences
            "Seq<Seq<int>>",
            "Seq<Seq<nat>>",
            "Seq<Seq<u32>>",
            "Seq<Seq<i32>>",
            "Seq<Seq<u8>>",
            "Seq<Seq<i8>>",
        }

        # Valid Rust native types for executable functions
        self.valid_rust_types = {
            "i8",
            "i16",
            "i32",
            "i64",
            "i128",
            "isize",
            "u8",
            "u16",
            "u32",
            "u64",
            "u128",
            "usize",
            "f32",
            "f64",
            "bool",
            "char",
            "str",
            "Vec<i8>",
            "Vec<i16>",
            "Vec<i32>",
            "Vec<i64>",
            "Vec<i128>",
            "Vec<u8>",
            "Vec<u16>",
            "Vec<u32>",
            "Vec<u64>",
            "Vec<u128>",
            "Vec<bool>",
            "Vec<char>",
            "Vec<Vec<i8>>",
            "Vec<Vec<i16>>",
            "Vec<Vec<i32>>",
            "Vec<Vec<i64>>",
            "Vec<Vec<u8>>",
            "Vec<Vec<u16>>",
            "Vec<Vec<u32>>",
            "Vec<Vec<u64>>",
            "Vec<Vec<bool>>",
            "Vec<Vec<char>>",
            "String",
            "Vec<String>",
            "Option<i8>",
            "Option<i16>",
            "Option<i32>",
            "Option<i64>",
            "Option<u8>",
            "Option<u16>",
            "Option<u32>",
            "Option<u64>",
        }

        # Pattern to match function signatures in vc-spec sections
        self.fn_pattern = re.compile(
            r"^\s*fn\s+(\w+)\s*\([^)]*\)\s*->\s*\([^)]*\)", re.MULTILINE
        )
        self.param_pattern = re.compile(r"(\w+):\s*([^,)]+)")
        self.return_pattern = re.compile(r"->\s*\(\s*(\w+):\s*([^)]+)\s*\)")

    def extract_vc_spec(self, yaml_content: dict) -> str:
        """Extract the vc-spec section from YAML content."""
        return (
            yaml_content.get("vc-spec", "")
            if isinstance(yaml_content.get("vc-spec"), str)
            else ""
        )

    def find_function_signatures(self, vc_spec: str) -> List[Tuple[str, str, int]]:
        """Find all function signatures in vc-spec content."""
        functions = []
        lines = vc_spec.split("\n")

        for i, line in enumerate(lines, 1):
            # Look for function definitions
            fn_match = re.search(r"^\s*fn\s+(\w+)\s*\(", line)
            if fn_match:
                func_name = fn_match.group(1)
                # Collect the full signature (may span multiple lines)
                signature_lines = []
                j = i - 1
                while j < len(lines):
                    signature_lines.append(lines[j])
                    # Stop when we find the opening brace or end of ensures/requires
                    if "{" in lines[j] or (
                        j + 1 < len(lines) and lines[j + 1].strip().startswith("{")
                    ):
                        break
                    if j + 1 < len(lines) and not lines[j + 1].strip():
                        break
                    j += 1

                signature = "\n".join(signature_lines)
                functions.append((func_name, signature, i))

        return functions

    def extract_types_from_signature(
        self, signature: str
    ) -> Tuple[List[str], List[str]]:
        """Extract parameter types and return types from function signature."""
        param_types = []
        return_types = []

        # Extract parameter types
        # Look for patterns like "param: Type" within parentheses
        param_section = re.search(r"\(([^)]*)\)", signature)
        if param_section:
            params_str = param_section.group(1)
            for param_match in self.param_pattern.finditer(params_str):
                param_type = param_match.group(2).strip()
                param_types.append(param_type)

        # Extract return types
        return_match = self.return_pattern.search(signature)
        if return_match:
            return_type = return_match.group(2).strip()
            return_types.append(return_type)

        return param_types, return_types

    def check_type_validity(self, type_str: str) -> Tuple[bool, str]:
        """Check if a type is valid for executable functions."""
        # Clean up the type string
        type_str = type_str.strip()

        # Check for forbidden mathematical types
        for forbidden in self.forbidden_types:
            if forbidden in type_str:
                suggestion = self.suggest_replacement(forbidden)
                return (
                    False,
                    f"Contains forbidden mathematical type '{forbidden}'. Suggest: {suggestion}",
                )

        # Check for bare int/nat which should be i8/u8
        if re.match(r"^int$", type_str):
            return False, "Use 'i8' instead of 'int' in executable functions"
        if re.match(r"^nat$", type_str):
            return False, "Use 'u8' instead of 'nat' in executable functions"

        return True, "OK"

    def suggest_replacement(self, forbidden_type: str) -> str:
        """Suggest a Rust native type replacement for forbidden mathematical types."""
        replacements = {
            "Seq<int>": "Vec<i8>",
            "Seq<nat>": "Vec<u8>",
            "Seq<i32>": "Vec<i8>",
            "Seq<u32>": "Vec<u8>",
            "Seq<Seq<int>>": "Vec<Vec<i8>>",
            "Seq<Seq<nat>>": "Vec<Vec<u8>>",
            "Seq<Seq<i32>>": "Vec<Vec<i8>>",
            "Seq<Seq<u32>>": "Vec<Vec<u8>>",
            "int": "i8",
            "nat": "u8",
        }
        return replacements.get(forbidden_type, "appropriate Rust native type")

    def check_yaml_file(self, file_path: Path) -> List[TypeIssue]:
        """Check a single YAML file for type issues."""
        issues = []

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Parse YAML
            yaml_content = yaml.safe_load(content)
            if not yaml_content:
                return issues

            # Extract vc-spec section
            vc_spec = self.extract_vc_spec(yaml_content)
            if not vc_spec:
                return issues

            # Find function signatures
            functions = self.find_function_signatures(vc_spec)

            for func_name, signature, line_num in functions:
                param_types, return_types = self.extract_types_from_signature(signature)

                # Check parameter types
                for param_type in param_types:
                    is_valid, message = self.check_type_validity(param_type)
                    if not is_valid:
                        issues.append(
                            TypeIssue(
                                file_path=str(file_path),
                                function_name=func_name,
                                issue_type=f"Parameter type: {param_type}",
                                line_number=line_num,
                                line_content=signature.split("\n")[0],
                                suggestion=message,
                            )
                        )

                # Check return types
                for return_type in return_types:
                    is_valid, message = self.check_type_validity(return_type)
                    if not is_valid:
                        issues.append(
                            TypeIssue(
                                file_path=str(file_path),
                                function_name=func_name,
                                issue_type=f"Return type: {return_type}",
                                line_number=line_num,
                                line_content=signature.split("\n")[0],
                                suggestion=message,
                            )
                        )

        except Exception as e:
            issues.append(
                TypeIssue(
                    file_path=str(file_path),
                    function_name="N/A",
                    issue_type="File parsing error",
                    line_number=0,
                    line_content="",
                    suggestion=f"Error: {str(e)}",
                )
            )

        return issues

    def check_directory(
        self, directory: Path, pattern: str = "*.yaml"
    ) -> List[TypeIssue]:
        """Check all YAML files in a directory for type issues."""
        all_issues = []

        yaml_files = list(directory.rglob(pattern))

        for yaml_file in yaml_files:
            file_issues = self.check_yaml_file(yaml_file)
            all_issues.extend(file_issues)

        return all_issues


def main():
    parser = argparse.ArgumentParser(
        description="Check Verus YAML files for proper Rust native types in executable functions"
    )
    parser.add_argument("path", help="Path to YAML file or directory to check")
    parser.add_argument(
        "--pattern", default="*.yaml", help="File pattern to match (default: *.yaml)"
    )
    parser.add_argument(
        "--summary", action="store_true", help="Show only summary statistics"
    )
    parser.add_argument(
        "--list-issues",
        action="store_true",
        help="Only list files with type issues (no statistics)",
    )
    parser.add_argument(
        "--quiet", action="store_true", help="Quiet mode: minimal output"
    )
    parser.add_argument(
        "--output", choices=["text", "json"], default="text", help="Output format"
    )

    args = parser.parse_args()

    checker = VerusTypeChecker()
    path = Path(args.path)

    if path.is_file():
        issues = checker.check_yaml_file(path)
        total_files = 1
    elif path.is_dir():
        issues = checker.check_directory(path, args.pattern)
        total_files = len(list(path.rglob(args.pattern)))
    else:
        print(f"Error: {path} is not a valid file or directory")
        return 1

    # Group issues by file
    issues_by_file = {}
    for issue in issues:
        if issue.file_path not in issues_by_file:
            issues_by_file[issue.file_path] = []
        issues_by_file[issue.file_path].append(issue)

    # Output results
    if args.output == "json":
        import json

        result = {
            "summary": {
                "total_files": total_files,
                "files_with_issues": len(issues_by_file),
                "total_issues": len(issues),
            },
            "issues": [
                {
                    "file": issue.file_path,
                    "function": issue.function_name,
                    "issue_type": issue.issue_type,
                    "line": issue.line_number,
                    "suggestion": issue.suggestion,
                }
                for issue in issues
            ],
        }
        print(json.dumps(result, indent=2))
    else:
        # Text output
        if not args.summary:
            if issues:
                print("🔍 Type Issues Found:")
                print("=" * 80)

                for file_path, file_issues in issues_by_file.items():
                    print(f"\n📁 File: {file_path}")
                    for issue in file_issues:
                        print(f"  ❌ Function: {issue.function_name}")
                        print(f"     Issue: {issue.issue_type}")
                        print(f"     Line {issue.line_number}: {issue.line_content}")
                        print(f"     💡 {issue.suggestion}")
                        print()
            else:
                print(
                    "✅ No type issues found! All executable functions use proper Rust native types."
                )

        # Summary
        print("\n📊 Summary:")
        print(f"  Total files checked: {total_files}")
        print(f"  Files with issues: {len(issues_by_file)}")
        print(f"  Total issues: {len(issues)}")

        if issues:
            print("\n🎯 Quick Stats:")
            issue_types = {}
            for issue in issues:
                key = (
                    issue.issue_type.split(":")[0]
                    if ":" in issue.issue_type
                    else issue.issue_type
                )
                issue_types[key] = issue_types.get(key, 0) + 1

            for issue_type, count in sorted(issue_types.items()):
                print(f"  {issue_type}: {count}")

    return 1 if issues else 0


if __name__ == "__main__":
    exit(main())
