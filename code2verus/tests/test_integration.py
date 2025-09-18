"""Integration tests for end-to-end functionality"""

import pytest
import tempfile
import asyncio
from pathlib import Path
from unittest.mock import patch, Mock
import yaml

from code2verus.processing import main_async
from code2verus import main


class TestEndToEndTranslation:
    """Test complete translation pipeline"""

    @pytest.fixture
    def sample_dafny_benchmark(self):
        """Create a sample Dafny benchmark directory"""
        with tempfile.TemporaryDirectory() as tmpdir:
            bench_dir = Path(tmpdir) / "sample_bench"
            bench_dir.mkdir()

            # Create sample Dafny files
            (bench_dir / "simple.dfy").write_text("""
function method add(x: int, y: int): int
{
    x + y
}

method testAdd()
{
    assert add(2, 3) == 5;
}
""")

            (bench_dir / "complex.dfy").write_text("""
method Max(a: int, b: int) returns (c: int)
    ensures c >= a && c >= b && (c == a || c == b)
{
    if a >= b {
        c := a;
    } else {
        c := b;
    }
}
""")

            yield str(bench_dir)

    @pytest.fixture
    def sample_lean_yaml_benchmark(self):
        """Create a sample Lean YAML benchmark directory"""
        with tempfile.TemporaryDirectory() as tmpdir:
            bench_dir = Path(tmpdir) / "lean_yaml_bench"
            bench_dir.mkdir()

            # Create sample Lean YAML file
            lean_yaml = {
                "vc-description": "Test arithmetic function",
                "vc-preamble": "import Mathlib",
                "vc-helpers": "-- helpers",
                "vc-signature": "def add (x y : Int) : Int :=",
                "vc-implementation": "x + y",
                "vc-condition": "theorem add_spec : add x y = x + y := by",
                "vc-proof": "simp [add]",
                "vc-postamble": "-- end",
            }

            yaml_file = bench_dir / "add_function.yaml"
            yaml_file.write_text(yaml.dump(lean_yaml))

            yield str(bench_dir)

    @pytest.mark.asyncio
    async def test_full_dafny_pipeline(self, sample_dafny_benchmark):
        """Test complete Dafny to Verus translation pipeline"""
        with patch("code2verus.agent.create_agent") as mock_create_agent:
            # Mock successful translation
            mock_agent = Mock()
            mock_result = Mock()
            mock_result.output = """use vstd::prelude::*;

verus! {
    fn add(x: i32, y: i32) -> i32 {
        x + y
    }
    
    proof fn test_add() {
        assert(add(2, 3) == 5);
    }
}

fn main() {}"""
            mock_result.all_messages = Mock(return_value=[])
            mock_agent.run = Mock(return_value=mock_result)
            mock_create_agent.return_value = mock_agent

            with patch("code2verus.verification.verify_verus_code") as mock_verify:
                mock_verify.return_value = True

                # Run the pipeline
                await main_async(
                    benchmark_path=sample_dafny_benchmark,
                    source_language="dafny",
                    max_concurrent=1,
                )

                # Verify translation was attempted
                assert mock_agent.run.call_count >= 1

    @pytest.mark.asyncio
    async def test_full_lean_yaml_pipeline(self, sample_lean_yaml_benchmark):
        """Test complete Lean YAML to Verus YAML translation pipeline"""
        with patch("code2verus.agent.create_agent") as mock_create_agent:
            # Mock successful YAML translation
            mock_agent = Mock()
            mock_result = Mock()
            mock_result.output = """vc-description: |-
  Test arithmetic function
vc-preamble: |-
  use vstd::prelude::*;
  verus! {
vc-helpers: |-

vc-spec: |-
  fn add(x: i32, y: i32) -> (result: i32)
      ensures result == x + y
vc-code: |-
  {
      // impl-start
      assume(false);
      0
      // impl-end
  }
vc-postamble: |-
  }
  fn main() {}"""
            mock_result.all_messages = Mock(return_value=[])
            mock_agent.run = Mock(return_value=mock_result)
            mock_create_agent.return_value = mock_agent

            # Run the pipeline
            await main_async(
                benchmark_path=sample_lean_yaml_benchmark,
                source_language="lean",
                max_concurrent=1,
                file_pattern="*.yaml",
            )

            # Verify translation was attempted
            assert mock_agent.run.call_count >= 1

    @pytest.mark.asyncio
    async def test_concurrent_processing(self, sample_dafny_benchmark):
        """Test concurrent processing of multiple files"""
        with patch("code2verus.agent.create_agent") as mock_create_agent:
            mock_agent = Mock()
            mock_result = Mock()
            mock_result.output = "// Mock translation"
            mock_result.all_messages = Mock(return_value=[])
            mock_agent.run = Mock(return_value=mock_result)
            mock_create_agent.return_value = mock_agent

            with patch("code2verus.verification.verify_verus_code") as mock_verify:
                mock_verify.return_value = True

                # Run with multiple concurrent tasks
                await main_async(
                    benchmark_path=sample_dafny_benchmark,
                    source_language="dafny",
                    max_concurrent=3,
                )

                # Should have processed multiple files
                assert mock_agent.run.call_count >= 2

    @pytest.mark.asyncio
    async def test_error_handling_in_pipeline(self, sample_dafny_benchmark):
        """Test error handling in the translation pipeline"""
        with patch("code2verus.agent.create_agent") as mock_create_agent:
            # Mock translation failure
            mock_agent = Mock()
            mock_agent.run = Mock(side_effect=Exception("API Error"))
            mock_create_agent.return_value = mock_agent

            # Pipeline should handle errors gracefully
            await main_async(
                benchmark_path=sample_dafny_benchmark,
                source_language="dafny",
                max_concurrent=1,
            )

            # Should have attempted translation despite errors
            assert mock_agent.run.call_count >= 1

    def test_cli_integration(self, sample_dafny_benchmark):
        """Test CLI integration"""
        with patch(
            "sys.argv",
            [
                "code2verus",
                "--benchmark",
                sample_dafny_benchmark,
                "--max-concurrent",
                "1",
            ],
        ):
            with patch("code2verus.processing.main_async") as mock_main_async:
                with patch(
                    "code2verus.utils.check_verus_availability"
                ) as mock_check_verus:
                    mock_check_verus.return_value = True

                    # This should not raise an exception
                    try:
                        main()
                    except SystemExit:
                        pass  # Expected for successful CLI execution

                    mock_main_async.assert_called_once()


class TestRegressionPrevention:
    """Test to prevent regressions in known working examples"""

    @pytest.fixture
    def known_good_dafny_examples(self):
        """Known good Dafny examples that should always work"""
        return {
            "simple_function": """
function method identity(x: int): int
{
    x
}
""",
            "basic_method": """
method Increment(x: int) returns (y: int)
    ensures y == x + 1
{
    y := x + 1;
}
""",
            "simple_loop": """
method Sum(n: nat) returns (s: int)
    ensures s == n * (n + 1) / 2
{
    s := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant s == i * (i + 1) / 2
    {
        i := i + 1;
        s := s + i;
    }
}
""",
        }

    @pytest.fixture
    def known_good_lean_examples(self):
        """Known good Lean examples that should always work"""
        return {
            "simple_function": """
def identity (x : Int) : Int := x
""",
            "theorem_example": """
theorem add_comm (x y : Int) : x + y = y + x := by
  ring
""",
            "inductive_proof": """
def factorial : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * factorial n

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial]; exact Nat.mul_pos (Nat.succ_pos _) ih
""",
        }

    @pytest.mark.asyncio
    async def test_dafny_examples_regression(self, known_good_dafny_examples):
        """Test that known good Dafny examples don't regress"""
        for name, code in known_good_dafny_examples.items():
            with patch("code2verus.agent.create_agent") as mock_create_agent:
                mock_agent = Mock()
                mock_result = Mock()
                mock_result.output = f"// Translated {name}"
                mock_result.all_messages = Mock(return_value=[])
                mock_agent.run = Mock(return_value=mock_result)
                mock_create_agent.return_value = mock_agent

                from code2verus.agent import translate_code_to_verus

                # Should not raise an exception
                result = await translate_code_to_verus(
                    source_code=code, source_language="dafny", max_iterations=1
                )

                assert isinstance(result.output_content, str)
                assert len(result.output_content) > 0

    @pytest.mark.asyncio
    async def test_lean_examples_regression(self, known_good_lean_examples):
        """Test that known good Lean examples don't regress"""
        for name, code in known_good_lean_examples.items():
            with patch("code2verus.agent.create_agent") as mock_create_agent:
                mock_agent = Mock()
                mock_result = Mock()
                mock_result.output = f"// Translated {name}"
                mock_result.all_messages = Mock(return_value=[])
                mock_agent.run = Mock(return_value=mock_result)
                mock_create_agent.return_value = mock_agent

                from code2verus.agent import translate_code_to_verus

                # Should not raise an exception
                result = await translate_code_to_verus(
                    source_code=code, source_language="lean", max_iterations=1
                )

                assert isinstance(result.output_content, str)
                assert len(result.output_content) > 0

    def test_config_stability(self):
        """Test that config structure remains stable"""
        from code2verus.config import cfg

        # Core config fields that should always exist
        required_fields = [
            "verus_path",
            "model",
            "max_translation_iterations",
            "max_retries",
            "system",
            "system_prompts",
            "yaml_instructions",
        ]

        for field in required_fields:
            assert field in cfg, f"Required config field missing: {field}"

        # Language-specific prompts
        assert "dafny" in cfg["system_prompts"]
        assert "lean" in cfg["system_prompts"]
        assert "dafny" in cfg["yaml_instructions"]
        assert "lean" in cfg["yaml_instructions"]

    def test_yaml_field_mapping_stability(self):
        """Test that YAML field mapping rules remain stable"""
        from code2verus.config import cfg

        lean_instructions = cfg["yaml_instructions"]["lean"]

        # Critical YAML mapping rules should be present
        critical_patterns = [
            "vc-spec",
            "vc-code",
            "assume(false)",
            "use vstd::prelude::*;",
            "verus! {",
            "fn main()",
        ]

        for pattern in critical_patterns:
            assert pattern in lean_instructions, (
                f"Critical YAML pattern missing: {pattern}"
            )


class TestPerformanceRegression:
    """Test to catch performance regressions"""

    @pytest.mark.asyncio
    async def test_translation_performance(self):
        """Test that translation doesn't take too long"""
        import time

        simple_code = "function method test(): int { 42 }"

        with patch("code2verus.agent.create_agent") as mock_create_agent:
            mock_agent = Mock()
            mock_result = Mock()
            mock_result.output = "// Fast translation"
            mock_result.all_messages = Mock(return_value=[])
            mock_agent.run = Mock(return_value=mock_result)
            mock_create_agent.return_value = mock_agent

            start_time = time.time()

            from code2verus.agent import translate_code_to_verus

            await translate_code_to_verus(
                source_code=simple_code, source_language="dafny", max_iterations=1
            )

            elapsed = time.time() - start_time

            # Translation (mocked) should complete quickly
            assert elapsed < 1.0, f"Translation took too long: {elapsed}s"

    @pytest.mark.asyncio
    async def test_concurrent_processing_performance(self):
        """Test concurrent processing performance"""
        import time

        items = [
            {"ground_truth": f"// Test {i}", "test_file": f"test_{i}.dfy"}
            for i in range(5)
        ]

        with patch("code2verus.processing.translate_code_to_verus") as mock_translate:
            mock_translate.return_value = "// Mock result"

            with patch("code2verus.processing.verify_verus_code") as mock_verify:
                mock_verify.return_value = True

                start_time = time.time()

                from code2verus.processing import process_item

                tasks = [
                    process_item(
                        i,
                        item,
                        source_language="dafny",
                        benchmark_name="test_benchmark",
                        max_retries=1,
                    )
                    for i, item in enumerate(items)
                ]

                results = await asyncio.gather(*tasks, return_exceptions=True)

                elapsed = time.time() - start_time

                # Concurrent processing should be reasonably fast
                assert elapsed < 2.0, f"Concurrent processing took too long: {elapsed}s"
                assert len(results) == len(items)
