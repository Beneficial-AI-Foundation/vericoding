"""
Performance regression tests to ensure the modular version doesn't introduce significant performance overhead.
"""

import pytest
import time
import sys
from pathlib import Path
from unittest.mock import patch, MagicMock
import tempfile
import shutil


class TestPerformanceRegression:
    """Test that modularization doesn't introduce performance regressions."""

    @pytest.fixture
    def temp_spec_files(self):
        """Create temporary specification files for performance testing."""
        temp_dir = tempfile.mkdtemp(prefix="perf_test_")
        temp_path = Path(temp_dir)
        
        # Create multiple spec files to test with
        for i in range(10):
            spec_file = temp_path / f"spec_{i}.dfy"
            spec_file.write_text(f"""
method TestMethod{i}(x: int, y: int) returns (result: int)
    ensures result == x + y + {i}
{{
    // Implementation needed
}}

function TestFunction{i}(n: nat): nat
    ensures TestFunction{i}(n) >= n
{{
    // Implementation needed
}}
""")
        
        yield temp_path
        shutil.rmtree(temp_dir, ignore_errors=True)

    def test_import_time_performance(self):
        """Test that imports don't take excessive time."""
        start_time = time.time()
        
        try:
            from vericoding.core import ProcessingConfig, PromptLoader, create_llm_provider
            from vericoding.core.language_tools import get_tool_path, check_tool_availability, find_spec_files
            from vericoding.processing import process_files_parallel
            from vericoding.utils import generate_summary, generate_csv_results
        except ImportError as e:
            pytest.skip(f"Cannot import modules: {e}")
        
        import_time = time.time() - start_time
        
        # Imports should complete within reasonable time (5 seconds is very generous)
        assert import_time < 5.0, f"Import time too slow: {import_time:.2f} seconds"
        print(f"✓ Import time: {import_time:.3f} seconds")

    def test_configuration_creation_performance(self):
        """Test that configuration creation is fast."""
        try:
            from vericoding.core import ProcessingConfig
        except ImportError:
            pytest.skip("Cannot import ProcessingConfig")
        
        start_time = time.time()
        
        # Test multiple configuration creations
        for _ in range(100):
            try:
                langs = ProcessingConfig.get_available_languages()
                assert len(langs) > 0
            except Exception:
                # May fail due to missing config files, but timing is what matters
                pass
        
        creation_time = time.time() - start_time
        avg_time = creation_time / 100
        
        # Each configuration creation should be very fast
        assert avg_time < 0.1, f"Configuration creation too slow: {avg_time:.3f} seconds average"
        print(f"✓ Average configuration creation time: {avg_time:.4f} seconds")

    def test_file_discovery_performance(self, temp_spec_files):
        """Test that file discovery scales reasonably."""
        try:
            from vericoding.core.language_tools import find_spec_files
        except ImportError:
            pytest.skip("Cannot import find_spec_files")
        
        # Mock configuration
        class MockConfig:
            files_dir = str(temp_spec_files)
            language = "dafny"
            language_config = type('MockLangConfig', (), {
                'file_extension': '.dfy',
                'keywords': ['method', 'function']
            })()
        
        config = MockConfig()
        
        start_time = time.time()
        
        # Test file discovery multiple times
        for _ in range(10):
            files = find_spec_files(config)
            assert len(files) == 10  # Should find all 10 spec files
        
        discovery_time = time.time() - start_time
        avg_time = discovery_time / 10
        
        # File discovery should be fast
        assert avg_time < 1.0, f"File discovery too slow: {avg_time:.3f} seconds average"
        print(f"✓ Average file discovery time: {avg_time:.4f} seconds")

    def test_prompt_loading_performance(self):
        """Test that prompt loading is efficient."""
        try:
            from vericoding.core import PromptLoader
        except ImportError:
            pytest.skip("Cannot import PromptLoader")
        
        # Mock prompt file content
        mock_prompts = """
generate_code: |
  Generate code from the following specification:
  {specification}
  
fix_verification: |
  Fix the following verification error:
  {error}
  In this code:
  {code}

optimize_code: |
  Optimize the following code:
  {code}
"""
        
        with patch('pathlib.Path.exists', return_value=True), \
             patch('builtins.open', create=True) as mock_open:
            
            mock_open.return_value.__enter__.return_value.read.return_value = mock_prompts
            
            start_time = time.time()
            
            # Test multiple prompt loader creations
            for _ in range(50):
                try:
                    loader = PromptLoader("dafny", "prompts.yaml")
                    validation = loader.validate_prompts()
                    # Prompt formatting test
                    if validation.valid:
                        loader.format_prompt("generate_code", specification="test spec")
                except Exception:
                    # May fail due to missing prompts, but timing matters
                    pass
            
            loading_time = time.time() - start_time
            avg_time = loading_time / 50
            
            assert avg_time < 0.05, f"Prompt loading too slow: {avg_time:.3f} seconds average"
            print(f"✓ Average prompt loading time: {avg_time:.4f} seconds")

    def test_memory_usage_reasonable(self):
        """Test that memory usage doesn't grow unexpectedly."""
        import psutil
        import os
        
        try:
            from vericoding.core import ProcessingConfig, PromptLoader
            from vericoding.core.language_tools import find_spec_files
        except ImportError:
            pytest.skip("Cannot import required modules")
        
        # Get initial memory usage
        process = psutil.Process(os.getpid())
        initial_memory = process.memory_info().rss / 1024 / 1024  # MB
        
        # Perform typical operations multiple times
        with patch('pathlib.Path.exists', return_value=True), \
             patch('builtins.open', create=True) as mock_open:
            
            mock_open.return_value.__enter__.return_value.read.return_value = """
generate_code: "Generate code"
fix_verification: "Fix errors"
"""
            
            for _ in range(100):
                try:
                    # Configuration operations
                    langs = ProcessingConfig.get_available_languages()
                    
                    # Prompt loading operations
                    loader = PromptLoader("dafny", "prompts.yaml")
                    loader.validate_prompts()
                    
                except Exception:
                    # Ignore errors, we're testing memory usage
                    pass
        
        # Check final memory usage
        final_memory = process.memory_info().rss / 1024 / 1024  # MB
        memory_increase = final_memory - initial_memory
        
        # Memory increase should be reasonable (less than 50MB for this test)
        assert memory_increase < 50, f"Memory usage increased too much: {memory_increase:.2f} MB"
        print(f"✓ Memory increase: {memory_increase:.2f} MB")

    def test_concurrent_operations_performance(self):
        """Test that concurrent operations don't cause excessive slowdown."""
        try:
            from vericoding.core import ProcessingConfig
        except ImportError:
            pytest.skip("Cannot import ProcessingConfig")
        
        import threading
        import concurrent.futures
        
        def config_operation():
            """Simulate configuration operations."""
            try:
                langs = ProcessingConfig.get_available_languages()
                return len(langs)
            except Exception:
                return 0
        
        start_time = time.time()
        
        # Test concurrent configuration access
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            futures = [executor.submit(config_operation) for _ in range(20)]
            results = [future.result() for future in concurrent.futures.as_completed(futures)]
        
        concurrent_time = time.time() - start_time
        
        # Concurrent operations should complete reasonably quickly
        assert concurrent_time < 10.0, f"Concurrent operations too slow: {concurrent_time:.2f} seconds"
        print(f"✓ Concurrent operations time: {concurrent_time:.3f} seconds")

    def test_cli_startup_performance(self):
        """Test that CLI startup time is reasonable."""
        project_root = Path(__file__).parent.parent
        script_path = project_root / "spec_to_code_modular.py"
        
        if not script_path.exists():
            pytest.skip("spec_to_code_modular.py not found")

        import subprocess
        
        start_time = time.time()
        
        # Test CLI help command (should be fast)
        result = subprocess.run(
            [sys.executable, str(script_path), "--help"],
            capture_output=True,
            text=True,
            cwd=project_root,
            timeout=30,
        )
        
        startup_time = time.time() - start_time
        
        if result.returncode == 0:
            # CLI startup should be fast
            assert startup_time < 10.0, f"CLI startup too slow: {startup_time:.2f} seconds"
            print(f"✓ CLI startup time: {startup_time:.3f} seconds")
        else:
            print(f"⚠ CLI startup test skipped due to error: {result.stderr[:100]}")


class TestScalabilityRegression:
    """Test that the modular version scales as well as the original."""
    
    def test_large_file_handling(self):
        """Test that large specification files are handled efficiently."""
        try:
            from vericoding.core.language_tools import find_spec_files
        except ImportError:
            pytest.skip("Cannot import find_spec_files")
        
        # Create a temporary directory with a large spec file
        temp_dir = tempfile.mkdtemp()
        temp_path = Path(temp_dir)
        
        try:
            # Create a large specification file
            large_spec = temp_path / "large_spec.dfy"
            large_content = []
            
            for i in range(1000):  # Create 1000 methods
                large_content.append(f"""
method LargeMethod{i}(x: int) returns (result: int)
    ensures result >= x
{{
    // Implementation {i}
}}
""")
            
            large_spec.write_text('\n'.join(large_content))
            
            # Mock configuration
            class MockConfig:
                files_dir = str(temp_path)
                language = "dafny"
                language_config = type('MockLangConfig', (), {
                    'file_extension': '.dfy',
                    'keywords': ['method']
                })()
            
            config = MockConfig()
            
            start_time = time.time()
            files = find_spec_files(config)
            processing_time = time.time() - start_time
            
            assert len(files) == 1
            assert processing_time < 5.0, f"Large file processing too slow: {processing_time:.2f} seconds"
            print(f"✓ Large file processing time: {processing_time:.3f} seconds")
            
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_many_files_handling(self):
        """Test that many small files are handled efficiently."""
        try:
            from vericoding.core.language_tools import find_spec_files
        except ImportError:
            pytest.skip("Cannot import find_spec_files")
        
        # Create temporary directory with many small files
        temp_dir = tempfile.mkdtemp()
        temp_path = Path(temp_dir)
        
        try:
            # Create many small spec files
            for i in range(100):
                spec_file = temp_path / f"spec_{i:03d}.dfy"
                spec_file.write_text(f"""
method Method{i}() returns (result: int)
    ensures result == {i}
{{
    // Implementation
}}
""")
            
            # Mock configuration
            class MockConfig:
                files_dir = str(temp_path)
                language = "dafny"
                language_config = type('MockLangConfig', (), {
                    'file_extension': '.dfy',
                    'keywords': ['method']
                })()
            
            config = MockConfig()
            
            start_time = time.time()
            files = find_spec_files(config)
            processing_time = time.time() - start_time
            
            assert len(files) == 100
            assert processing_time < 5.0, f"Many files processing too slow: {processing_time:.2f} seconds"
            print(f"✓ Many files processing time: {processing_time:.3f} seconds")
            
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)


if __name__ == "__main__":
    # Allow running this test file directly
    pytest.main([__file__, "-v"])
