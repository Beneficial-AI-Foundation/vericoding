"""Test benchmark loading and processing functionality"""

import pytest
import tempfile
from pathlib import Path
from unittest.mock import patch, Mock
import yaml

from code2verus.benchmarks import load_benchmark, is_flat_structure
from code2verus.processing import process_item, derive_output_path


@pytest.fixture
def sample_dafny_bench_item():
    """Sample DafnyBench format item"""
    return {
        "ground_truth": """function method add(x: int, y: int): int { x + y }""",
        "test_file": "basic/arithmetic.dfy",
        "id": "arithmetic_add"
    }


@pytest.fixture
def sample_verina_item():
    """Sample Verina format item"""
    return {
        "id": "verina_basic_70",
        "lean_code": """def add (x y : Int) : Int := x + y

theorem add_comm (x y : Int) : add x y = add y x := by
  simp [add]
  ring""",
        "metadata": {"difficulty": "basic"}
    }


@pytest.fixture
def sample_reform_item():
    """Sample ReForm-DafnyComp-Benchmark format item"""
    return {
        "org_input": """method Max(a: int, b: int) returns (c: int)
  ensures c >= a && c >= b && (c == a || c == b)
{
  if a >= b {
    c := a;
  } else {
    c := b;
  }
}""",
        "org_input_id": "max_function_001"
    }


class TestBenchmarkLoading:
    """Test benchmark loading functionality"""

    @patch('datasets.load_dataset')
    def test_load_huggingface_dataset(self, mock_load_dataset):
        """Test loading Hugging Face datasets"""
        mock_dataset = Mock()
        mock_dataset.__iter__ = Mock(return_value=iter([{"ground_truth": "test", "test_file": "test.dfy"}]))
        mock_load_dataset.return_value = {"test": mock_dataset}
        
        items = load_benchmark("wendy-sun/DafnyBench", "test")
        assert len(list(items)) == 1

    def test_load_local_directory(self, sample_dafny_bench_item):
        """Test loading from local directory"""
        with tempfile.TemporaryDirectory() as tmpdir:
            # Create test files
            test_dir = Path(tmpdir) / "test_bench"
            test_dir.mkdir()
            
            # Create a Dafny file
            dafny_file = test_dir / "test.dfy"
            dafny_file.write_text("function method test(): int { 42 }")
            
            # Create a Lean file
            lean_file = test_dir / "test.lean"
            lean_file.write_text("def test : Int := 42")
            
            # Test Dafny loading
            items = list(load_benchmark(str(test_dir), file_pattern="*.dfy"))
            assert len(items) >= 1
            assert any("function method test" in item.get("code", "") for item in items)
            
            # Test Lean loading
            items = list(load_benchmark(str(test_dir), file_pattern="*.lean"))
            assert len(items) >= 1
            assert any("def test" in item.get("code", "") for item in items)

    def test_load_yaml_files(self):
        """Test loading YAML files from local directory"""
        with tempfile.TemporaryDirectory() as tmpdir:
            test_dir = Path(tmpdir)
            
            # Create sample YAML file
            yaml_file = test_dir / "test.yaml"
            sample_yaml = {
                "vc-description": "Test YAML",
                "vc-preamble": "// test",
                "vc-signature": "def test() -> int",
                "vc-implementation": "42"
            }
            yaml_file.write_text(yaml.dump(sample_yaml))
            
            items = list(load_benchmark(str(test_dir), file_pattern="*.yaml"))
            assert len(items) >= 1
            assert "vc-description" in items[0]

    def test_is_flat_structure_detection(self):
        """Test detection of flat vs hierarchical directory structure"""
        with tempfile.TemporaryDirectory() as tmpdir:
            base_dir = Path(tmpdir)
            
            # Create flat structure dataset (all files in same directory)
            flat_dataset = [
                {"source_path": str(base_dir / "flat" / "file1.dfy")},
                {"source_path": str(base_dir / "flat" / "file2.dfy")}
            ]
            
            # Create hierarchical structure dataset (files in different directories)
            hierarchical_dataset = [
                {"source_path": str(base_dir / "hierarchical" / "file1.dfy")},
                {"source_path": str(base_dir / "hierarchical" / "subdir" / "file2.dfy")}
            ]
            
            # Test empty dataset
            empty_dataset = []
            
            assert is_flat_structure(flat_dataset, "test_flat")
            assert not is_flat_structure(hierarchical_dataset, "test_hierarchical")
            assert not is_flat_structure(empty_dataset, "test_empty")

    def test_empty_directory_handling(self):
        """Test handling of empty directories"""
        with tempfile.TemporaryDirectory() as tmpdir:
            empty_dir = Path(tmpdir) / "empty"
            empty_dir.mkdir()
            
            items = list(load_benchmark(str(empty_dir)))
            assert len(items) == 0

    @patch('datasets.load_dataset')
    def test_dataset_loading_errors(self, mock_load_dataset):
        """Test error handling in dataset loading"""
        mock_load_dataset.side_effect = Exception("Dataset not found")
        
        # Should handle gracefully
        items = list(load_benchmark("nonexistent/dataset"))
        assert len(items) == 0


class TestItemProcessing:
    """Test individual item processing"""

    @pytest.mark.asyncio
    async def test_process_dafny_bench_item(self, sample_dafny_bench_item):
        """Test processing DafnyBench format item"""
        with patch('code2verus.processing.translate_code_to_verus') as mock_translate:
            mock_translate.return_value = "// Translated Verus code"
            
            with patch('code2verus.processing.verify_verus_code') as mock_verify:
                mock_verify.return_value = True
                
                result = await process_item(
                    idx=0,
                    item=sample_dafny_bench_item,
                    source_language="dafny",
                    benchmark_name="test",
                    max_retries=1
                )
                
                assert result["success"]
                mock_translate.assert_called_once()

    @pytest.mark.asyncio
    async def test_process_verina_item(self, sample_verina_item):
        """Test processing Verina format item"""
        with patch('code2verus.processing.translate_code_to_verus') as mock_translate:
            mock_translate.return_value = "// Translated Verus code"
            
            with patch('code2verus.processing.verify_verus_code') as mock_verify:
                mock_verify.return_value = True
                
                result = await process_item(
                    idx=0,
                    item=sample_verina_item,
                    source_language="lean",
                    benchmark_name="verina",
                    max_retries=1
                )
                
                assert result["success"]
                assert "verina_basic_70" in str(result.get("output_path", ""))

    @pytest.mark.asyncio
    async def test_process_reform_item(self, sample_reform_item):
        """Test processing ReForm-DafnyComp-Benchmark format item"""
        with patch('code2verus.processing.translate_code_to_verus') as mock_translate:
            mock_translate.return_value = "// Translated Verus code"
            
            with patch('code2verus.processing.verify_verus_code') as mock_verify:
                mock_verify.return_value = True
                
                result = await process_item(
                    idx=0,
                    item=sample_reform_item,
                    source_language="dafny", 
                    benchmark_name="reform",
                    max_retries=1
                )
                
                assert result["success"]
                mock_translate.assert_called_once()

    @pytest.mark.asyncio
    async def test_process_item_translation_failure(self, sample_dafny_bench_item):
        """Test handling of translation failures"""
        with patch('code2verus.processing.translate_code_to_verus') as mock_translate:
            mock_translate.side_effect = Exception("Translation failed")
            
            result = await process_item(
                idx=0,
                item=sample_dafny_bench_item,
                source_language="dafny",
                benchmark_name="test",
                max_retries=1
            )
            
            assert not result["success"]
            assert "error" in result

    @pytest.mark.asyncio
    async def test_process_item_verification_failure(self, sample_dafny_bench_item):
        """Test handling of verification failures"""
        with patch('code2verus.processing.translate_code_to_verus') as mock_translate:
            mock_translate.return_value = "// Invalid Verus code"
            
            with patch('code2verus.processing.verify_verus_code') as mock_verify:
                mock_verify.return_value = False
                
                result = await process_item(
                    idx=0,
                    item=sample_dafny_bench_item,
                    source_language="dafny",
                    benchmark_name="test",
                    max_retries=1
                )
                
                assert not result["success"]

    @pytest.mark.asyncio
    async def test_process_yaml_item(self):
        """Test processing YAML format items"""
        yaml_item = {
            "vc-description": "Test function",
            "vc-signature": "def test() -> int",
            "vc-implementation": "42"
        }
        
        with patch('code2verus.processing.translate_code_to_verus') as mock_translate:
            mock_translate.return_value = """vc-description: |-
  Test function
vc-spec: |-
  fn test() -> i32 { 42 }"""
            
            with patch('code2verus.processing.verify_verus_code') as mock_verify:
                mock_verify.return_value = True
                
                result = await process_item(
                    idx=0,
                    item=yaml_item,
                    source_language="dafny",
                    benchmark_name="test",
                    is_yaml=True,
                    max_retries=1
                )
                
                assert result["success"]


class TestOutputPathDerivation:
    """Test output path derivation logic"""

    def test_derive_output_path_lean_benchmark(self):
        """Test output path derivation for Lean benchmarks"""
        benchmark_path = "/home/user/benchmarks/lean/test_bench"
        result = derive_output_path(benchmark_path, "test_bench", is_yaml=False)
        
        expected = Path("/home/user/benchmarks/verus/test_bench/files")
        assert result == expected

    def test_derive_output_path_lean_yaml(self):
        """Test output path derivation for Lean YAML files"""
        benchmark_path = "/home/user/benchmarks/lean/test_bench"
        result = derive_output_path(benchmark_path, "test_bench", is_yaml=True)
        
        expected = Path("/home/user/benchmarks/verus/test_bench/yaml")
        assert result == expected

    def test_derive_output_path_fallback(self):
        """Test output path derivation fallback for non-Lean benchmarks"""
        from code2verus.config import ARTIFACTS
        
        benchmark_path = "/some/other/path"
        result = derive_output_path(benchmark_path, "other_bench", is_yaml=False)
        
        expected = ARTIFACTS / "other_bench"
        assert result == expected

    def test_derive_output_path_edge_cases(self):
        """Test edge cases in output path derivation"""
        # Empty path
        result = derive_output_path("", "empty", is_yaml=False)
        assert isinstance(result, Path)
        
        # Relative path
        result = derive_output_path("./relative/path", "relative", is_yaml=False)
        assert isinstance(result, Path)


class TestBenchmarkCompatibility:
    """Test compatibility with different benchmark formats"""

    def test_dafny_bench_compatibility(self, sample_dafny_bench_item):
        """Test compatibility with DafnyBench format"""
        required_fields = ["ground_truth", "test_file"]
        for field in required_fields:
            assert field in sample_dafny_bench_item

    def test_verina_compatibility(self, sample_verina_item):
        """Test compatibility with Verina format"""
        required_fields = ["id", "lean_code"]
        for field in required_fields:
            assert field in sample_verina_item

    def test_reform_compatibility(self, sample_reform_item):
        """Test compatibility with ReForm format"""
        required_fields = ["org_input", "org_input_id"]
        for field in required_fields:
            assert field in sample_reform_item
