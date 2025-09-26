"""LLM-based failure analyzer for post-hoc analysis of verification failures."""

import os
import json
import pandas as pd
from typing import Dict, List, Optional, Any
import wandb

from ..core.llm_providers import create_llm_provider


class FailureAnalyzer:
    """Analyzes verification failures using LLM to identify patterns and suggest fixes."""

    def __init__(
        self, project_name: Optional[str] = None, llm_provider: str = "claude"
    ):
        """Initialize failure analyzer."""
        self.project_name = project_name or os.getenv("WANDB_PROJECT", "vericoding")
        self.entity = os.getenv("WANDB_ENTITY")
        self.llm_provider = llm_provider
        self.api = wandb.Api() if wandb.run or os.getenv("WANDB_API_KEY") else None
        self.analysis_results = []

    def analyze_run(self, run_id: str) -> Dict[str, Any]:
        """Analyze all failures from a specific wandb run."""
        if not self.api:
            raise ValueError("wandb API not available. Set WANDB_API_KEY.")

        # Retrieve run
        run_path = (
            f"{self.entity}/{self.project_name}/{run_id}"
            if self.entity
            else f"{self.project_name}/{run_id}"
        )
        run = self.api.run(run_path)

        # Get failure table from run history
        failures = []
        for row in run.scan_history(keys=["verification_failures"]):
            if "verification_failures" in row:
                # Extract table data
                table_data = row["verification_failures"]
                if hasattr(table_data, "data"):
                    failures.extend(table_data.data)

        if not failures:
            return {"status": "no_failures", "run_id": run_id}

        # Convert to DataFrame for analysis
        failures_df = pd.DataFrame(
            failures,
            columns=[
                "file",
                "iteration",
                "spec_hash",
                "code_hash",
                "error_category",
                "error_msg",
                "proof_state",
                "timestamp",
            ],
        )

        # Analyze unique failure patterns
        analysis = self._analyze_failure_patterns(failures_df)

        # Generate fix suggestions for top errors
        suggestions = self._generate_fix_suggestions(failures_df)

        # Create analysis report
        report = {
            "run_id": run_id,
            "total_failures": len(failures_df),
            "unique_errors": len(failures_df["error_msg"].unique()),
            "error_distribution": analysis["error_categories"],
            "problematic_files": analysis["problematic_files"],
            "suggested_fixes": suggestions,
            "patterns": analysis["patterns"],
        }

        # Log analysis results to wandb
        self._log_analysis_to_wandb(report)

        return report

    def _analyze_failure_patterns(self, failures_df: pd.DataFrame) -> Dict[str, Any]:
        """Analyze patterns in failures."""
        # Error category distribution
        error_categories = failures_df["error_category"].value_counts().to_dict()

        # Files with most failures
        file_failures = failures_df.groupby("file").size().sort_values(ascending=False)
        problematic_files = file_failures.head(5).to_dict()

        # Iteration patterns (do errors happen early or late?)
        avg_failure_iteration = failures_df["iteration"].mean()

        # Find recurring error messages
        error_counts = failures_df["error_msg"].value_counts()
        recurring_errors = error_counts[error_counts > 1].head(10).to_dict()

        # Identify patterns using simple heuristics
        patterns = []

        # Pattern: Files that always fail at same iteration
        for file in failures_df["file"].unique():
            file_data = failures_df[failures_df["file"] == file]
            if len(file_data) > 1 and file_data["iteration"].nunique() == 1:
                patterns.append(
                    {
                        "type": "stuck_at_iteration",
                        "file": file,
                        "iteration": file_data["iteration"].iloc[0],
                    }
                )

        # Pattern: Files with escalating errors
        for file in failures_df["file"].unique():
            file_data = failures_df[failures_df["file"] == file].sort_values(
                "iteration"
            )
            if len(file_data) > 2:
                iterations = file_data["iteration"].tolist()
                if iterations == sorted(iterations):
                    patterns.append(
                        {
                            "type": "escalating_failures",
                            "file": file,
                            "iterations": iterations,
                        }
                    )

        return {
            "error_categories": error_categories,
            "problematic_files": problematic_files,
            "avg_failure_iteration": avg_failure_iteration,
            "recurring_errors": recurring_errors,
            "patterns": patterns,
        }

    def _generate_fix_suggestions(
        self, failures_df: pd.DataFrame, max_suggestions: int = 5
    ) -> List[Dict[str, Any]]:
        """Use LLM to generate fix suggestions for most common failures."""
        # Get unique error patterns
        unique_errors = (
            failures_df.groupby(["error_msg", "proof_state"])
            .size()
            .sort_values(ascending=False)
        )

        suggestions = []
        llm = create_llm_provider(self.llm_provider)

        for (error_msg, proof_state), count in unique_errors.head(
            max_suggestions
        ).items():
            # Create analysis prompt
            prompt = self._create_analysis_prompt(error_msg, proof_state)

            try:
                # Get LLM analysis
                response = llm.call_api(prompt)
                analysis = self._parse_llm_response(response)

                suggestions.append(
                    {
                        "error": error_msg,  # Don't truncate error messages
                        "occurrences": int(count),
                        "root_cause": analysis.get("root_cause", "Unknown"),
                        "fix_strategy": analysis.get("fix_strategy", "No suggestion"),
                        "confidence": analysis.get("confidence", 0.5),
                    }
                )
            except Exception as e:
                print(f"Error analyzing failure: {e}")
                continue

        return suggestions

    def _create_analysis_prompt(self, error_msg: str, proof_state: str) -> str:
        """Create prompt for LLM failure analysis."""
        return f"""Analyze this Lean verification failure and provide actionable insights.

ERROR MESSAGE:
{error_msg}

PROOF STATE (if available):
{proof_state if proof_state else "Not provided"}

Please analyze and respond with a JSON object containing:
1. "root_cause": One of ["type_mismatch", "missing_lemma", "wrong_strategy", "incomplete_spec", "syntax_error", "timeout", "other"]
2. "fix_strategy": A concrete suggestion for fixing this error (1-2 sentences)
3. "confidence": Your confidence in the analysis (0.0 to 1.0)
4. "explanation": Brief explanation of why this error occurred

Respond only with the JSON object, no additional text."""

    def _parse_llm_response(self, response: str) -> Dict[str, Any]:
        """Parse LLM response to extract analysis."""
        try:
            # Try to extract JSON from response
            import re

            json_match = re.search(r"\{.*\}", response, re.DOTALL)
            if json_match:
                return json.loads(json_match.group())
        except (json.JSONDecodeError, AttributeError):
            pass

        # Fallback: basic parsing
        result = {
            "root_cause": "other",
            "fix_strategy": "Review the error message and proof state",
            "confidence": 0.3,
        }

        # Simple heuristic parsing
        if "type" in response.lower():
            result["root_cause"] = "type_mismatch"
        elif "lemma" in response.lower() or "theorem" in response.lower():
            result["root_cause"] = "missing_lemma"
        elif "strategy" in response.lower() or "tactic" in response.lower():
            result["root_cause"] = "wrong_strategy"

        return result

    def _log_analysis_to_wandb(self, report: Dict[str, Any]):
        """Log analysis results to wandb."""
        if not wandb.run:
            return

        # Create summary table
        summary_table = wandb.Table(columns=["metric", "value"])
        summary_table.add_data("Total Failures", report["total_failures"])
        summary_table.add_data("Unique Errors", report["unique_errors"])
        summary_table.add_data(
            "Most Common Error",
            list(report["error_distribution"].keys())[0]
            if report["error_distribution"]
            else "N/A",
        )

        wandb.log({"failure_analysis_summary": summary_table})

        # Create error distribution chart
        if report["error_distribution"]:
            data = [[k, v] for k, v in report["error_distribution"].items()]
            table = wandb.Table(data=data, columns=["Error Category", "Count"])
            wandb.log(
                {
                    "error_distribution": wandb.plot.bar(
                        table,
                        "Error Category",
                        "Count",
                        title="Verification Error Distribution",
                    )
                }
            )

        # Log suggested fixes
        if report["suggested_fixes"]:
            fixes_table = wandb.Table(
                columns=[
                    "error",
                    "occurrences",
                    "root_cause",
                    "fix_strategy",
                    "confidence",
                ]
            )
            for fix in report["suggested_fixes"]:
                fixes_table.add_data(
                    fix["error"],
                    fix["occurrences"],
                    fix["root_cause"],
                    fix["fix_strategy"],
                    fix["confidence"],
                )
            wandb.log({"suggested_fixes": fixes_table})

    def analyze_cross_run_patterns(self, last_n_runs: int = 10) -> Dict[str, Any]:
        """Analyze patterns across multiple runs."""
        if not self.api:
            raise ValueError("wandb API not available")

        # Get recent runs
        runs = self.api.runs(
            f"{self.entity}/{self.project_name}" if self.entity else self.project_name,
            filters={"state": "finished"},
            order="-created_at",
            per_page=last_n_runs,
        )

        all_failures = []
        run_summaries = []

        for run in runs:
            # Get failures from each run
            for row in run.scan_history(keys=["verification_failures"]):
                if "verification_failures" in row and hasattr(
                    row["verification_failures"], "data"
                ):
                    failures = row["verification_failures"].data
                    for failure in failures:
                        failure_dict = {
                            "run_id": run.id,
                            "run_name": run.name,
                            "file": failure[0],
                            "iteration": failure[1],
                            "error_category": failure[4]
                            if len(failure) > 4
                            else "unknown",
                            "error_msg": failure[5] if len(failure) > 5 else "",
                        }
                        all_failures.append(failure_dict)

            # Collect run summary
            if run.summary:
                run_summaries.append(
                    {
                        "run_id": run.id,
                        "success_rate": run.summary.get("success_rate", 0),
                        "total_files": run.summary.get("total_files", 0),
                    }
                )

        if not all_failures:
            return {"status": "no_failures_found"}

        # Analyze cross-run patterns
        failures_df = pd.DataFrame(all_failures)

        # Files that consistently fail across runs
        file_failure_rates = failures_df.groupby("file")["run_id"].nunique() / len(runs)
        problematic_files = file_failure_rates[file_failure_rates > 0.5].to_dict()

        # Error categories over time
        error_trends = (
            failures_df.groupby(["run_id", "error_category"])
            .size()
            .unstack(fill_value=0)
        )

        # Success rate trends
        avg_success_rate = (
            sum(r["success_rate"] for r in run_summaries) / len(run_summaries)
            if run_summaries
            else 0
        )

        return {
            "total_runs_analyzed": len(runs),
            "total_failures": len(all_failures),
            "consistently_failing_files": problematic_files,
            "avg_success_rate": avg_success_rate,
            "error_trends": error_trends.to_dict() if not error_trends.empty else {},
            "unique_failing_files": failures_df["file"].nunique(),
        }

    def generate_improvement_report(self, analysis: Dict[str, Any]) -> str:
        """Generate human-readable improvement recommendations."""
        report = ["# Verification Failure Analysis Report\n"]

        # Summary
        report.append("## Summary")
        report.append(f"- Total failures analyzed: {analysis.get('total_failures', 0)}")
        report.append(f"- Unique error types: {analysis.get('unique_errors', 0)}")
        report.append("")

        # Error distribution
        if "error_distribution" in analysis:
            report.append("## Error Distribution")
            for category, count in analysis["error_distribution"].items():
                report.append(f"- {category}: {count} occurrences")
            report.append("")

        # Problematic files
        if "problematic_files" in analysis:
            report.append("## Most Problematic Files")
            for file, count in list(analysis["problematic_files"].items())[:5]:
                report.append(f"- {file}: {count} failures")
            report.append("")

        # Suggested fixes
        if "suggested_fixes" in analysis:
            report.append("## Recommended Fixes")
            for i, fix in enumerate(analysis["suggested_fixes"], 1):
                report.append(f"\n### Issue {i}")
                report.append(f"**Error**: {fix['error']}")
                report.append(f"**Occurrences**: {fix['occurrences']}")
                report.append(f"**Root Cause**: {fix['root_cause']}")
                report.append(f"**Suggested Fix**: {fix['fix_strategy']}")
                report.append(f"**Confidence**: {fix['confidence']:.1%}")
            report.append("")

        # Patterns
        if "patterns" in analysis and analysis["patterns"]:
            report.append("## Identified Patterns")
            for pattern in analysis["patterns"]:
                if pattern["type"] == "stuck_at_iteration":
                    report.append(
                        f"- {pattern['file']} consistently fails at iteration {pattern['iteration']}"
                    )
                elif pattern["type"] == "escalating_failures":
                    report.append(
                        f"- {pattern['file']} shows escalating failures across iterations"
                    )
            report.append("")

        # Recommendations
        report.append("## General Recommendations")

        # Based on error distribution
        if "error_distribution" in analysis:
            top_error = max(
                analysis["error_distribution"], key=analysis["error_distribution"].get
            )
            if top_error == "type_mismatch":
                report.append(
                    "- Focus on type checking: Many failures are due to type mismatches"
                )
                report.append(
                    "- Consider adding more type annotations in specifications"
                )
            elif top_error == "missing_lemma":
                report.append(
                    "- Enhance lemma search: Many proofs fail due to missing lemmas"
                )
                report.append(
                    "- Consider building a lemma database from successful proofs"
                )
            elif top_error == "incomplete_proof":
                report.append(
                    "- Improve proof completion: Many proofs are left incomplete"
                )
                report.append(
                    "- Consider implementing proof sketch completion strategies"
                )

        report.append("")

        return "\n".join(report)
