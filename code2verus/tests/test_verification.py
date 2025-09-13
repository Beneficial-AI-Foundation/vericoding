"""Test Verus verification functionality"""

import asyncio
import pytest
import tempfile
from pathlib import Path
from unittest.mock import patch, Mock
import subprocess

from code2verus.verification import verify_verus_code
from code2verus.utils import check_verus_availability


# Configure pytest to handle async tests
pytestmark = pytest.mark.asyncio


@pytest.fixture
def valid_verus_code():
    """Valid Verus code that should compile"""
    return """use vstd::prelude::*;

verus! {
    fn add(x: u32, y: u32) -> u32 {
        x + y
    }
    
    proof fn test_add() {
        assert(add(2, 3) == 5);
    }
}

fn main() {}"""


@pytest.fixture
def invalid_verus_code():
    """Invalid Verus code that should not compile"""
    return """use vstd::prelude::*;

verus! {
    fn broken_function() -> i32 {
        // Missing return statement
    }
    
    proof fn invalid_proof() {
        assert(1 == 2); // This should fail
    }
}

fn main() {}"""


@pytest.fixture
def verus_syntax_error():
    """Verus code with syntax errors"""
    return """use vstd::prelude::*;

verus! {
    fn syntax_error( {  // Missing parameter and closing paren
        return 42
    }
}

fn main() {}"""


class TestVerusAvailability:
    """Test Verus installation and availability"""

    @patch('subprocess.run')
    def test_verus_available(self, mock_run):
        """Test detection of available Verus installation"""
        mock_run.return_value = Mock(returncode=0, stdout="Verus version 0.1.0")
        
        assert check_verus_availability()
        mock_run.assert_called_once()

    @patch('subprocess.run')
    def test_verus_not_available(self, mock_run):
        """Test detection when Verus is not available"""
        mock_run.side_effect = FileNotFoundError("verus command not found")
        
        assert not check_verus_availability()

    @patch('subprocess.run')
    def test_verus_command_fails(self, mock_run):
        """Test when Verus command fails"""
        mock_run.return_value = Mock(returncode=1, stderr="Verus error")
        
        assert not check_verus_availability()


class TestVerusVerification:
    """Test Verus code verification"""

    @patch('asyncio.create_subprocess_exec')
    async def test_verify_valid_code_success(self, mock_subprocess, valid_verus_code):
        """Test verification of valid Verus code"""
        # Mock the subprocess
        mock_process = Mock()
        mock_process.returncode = 0
        mock_process.communicate.return_value = (b"verification passed", b"")
        mock_subprocess.return_value = mock_process
        
        success, output, error = await verify_verus_code(valid_verus_code)
        
        assert success
        assert "verification passed" in output
        assert error == ""

    @patch('asyncio.create_subprocess_exec')
    async def test_verify_invalid_code_failure(self, mock_subprocess, invalid_verus_code):
        """Test verification of invalid Verus code"""
        # Mock the subprocess
        mock_process = Mock()
        mock_process.returncode = 1
        mock_process.communicate.return_value = (b"", b"verification failed: assertion might not hold")
        mock_subprocess.return_value = mock_process
        
        success, output, error = await verify_verus_code(invalid_verus_code)
        
        assert not success
        assert "verification failed" in error

    @patch('asyncio.create_subprocess_exec')
    async def test_verify_syntax_error(self, mock_subprocess, verus_syntax_error):
        """Test verification of code with syntax errors"""
        # Mock the subprocess
        mock_process = Mock()
        mock_process.returncode = 1
        mock_process.communicate.return_value = (b"", b"syntax error: expected `)` but found `{`")
        mock_subprocess.return_value = mock_process
        
        success, output, error = await verify_verus_code(verus_syntax_error)
        
        assert not success
        assert "syntax error" in error

    @patch('asyncio.wait_for')
    async def test_verify_timeout(self, mock_wait_for, valid_verus_code):
        """Test verification timeout handling"""
        mock_wait_for.side_effect = asyncio.TimeoutError()
        
        success, output, error = await verify_verus_code(valid_verus_code)
        
        assert not success
        assert "timeout" in error.lower() or "timed out" in error.lower()

    async def test_verify_nonexistent_file(self):
        """Test verification with empty/invalid code"""
        success, output, error = await verify_verus_code("")
        assert not success

    @patch('asyncio.create_subprocess_exec')
    async def test_verify_with_custom_verus_path(self, mock_subprocess, valid_verus_code):
        """Test verification with custom Verus path"""
        # Mock the subprocess
        mock_process = Mock()
        mock_process.returncode = 0
        mock_process.communicate.return_value = (b"success", b"")
        mock_subprocess.return_value = mock_process
        
        # Test with custom path
        with patch.dict('code2verus.config.cfg', {"verus_path": "/custom/path/to/verus"}):
            success, output, error = await verify_verus_code(valid_verus_code)
            assert success
            
            # Verify the custom path was used
            args = mock_subprocess.call_args[0]
            assert args[0] == "/custom/path/to/verus"


class TestVerificationIntegration:
    """Test verification integration with translation"""

    async def test_verification_in_translation_pipeline(self):
        """Test that verification is called in the translation pipeline"""
        # This would be called by the processing pipeline
        test_code = "fn test() { }"
        
        # Test with minimal valid Verus code
        valid_code = """use vstd::prelude::*;
verus! {
    fn test() -> u32 { 42 }
}
fn main() {}"""
        
        # Only test if Verus is available, otherwise skip
        if check_verus_availability():
            success, output, error = await verify_verus_code(valid_code)
            # We expect this to work if Verus is properly installed
            assert isinstance(success, bool)
            assert isinstance(output, str)
            assert isinstance(error, str)
        else:
            pytest.skip("Verus not available")

    async def test_known_good_examples_compile(self):
        """Test that known good examples from the codebase compile"""
        # Test some basic Verus patterns that should always work
        examples = [
            # Basic function
            """use vstd::prelude::*;
verus! {
    fn simple() -> u32 { 42 }
}
fn main() {}""",
            
            # Function with specification
            """use vstd::prelude::*;
verus! {
    fn add(x: u32, y: u32) -> (result: u32)
        ensures result == x + y
    {
        x + y
    }
}
fn main() {}""",
            
            # Proof function
            """use vstd::prelude::*;
verus! {
    proof fn basic_proof() {
        assert(2 + 2 == 4);
    }
}
fn main() {}""",
        ]
        
        for i, code in enumerate(examples):
            # Only run this test if Verus is actually available
            if check_verus_availability():
                success, output, error = await verify_verus_code(code)
                assert success, f"Example {i} failed to verify: {error}"
            else:
                pytest.skip("Verus not available")


class TestVerificationErrors:
    """Test various verification error cases"""

    @pytest.fixture
    def common_error_patterns(self):
        """Common Verus error patterns and their code"""
        return {
            "missing_main": """use vstd::prelude::*;
verus! {
    fn test() -> u32 { 42 }
}
// Missing fn main() {}""",
            
            "invalid_ensures": """use vstd::prelude::*;
verus! {
    fn bad_ensures(x: u32) -> (result: u32)
        ensures result == x + 1  // This will fail
    {
        x
    }
}
fn main() {}""",
            
            "spec_error": """use vstd::prelude::*;
verus! {
    spec fn bad_spec() -> int {
        1 / 0  // Division by zero in spec
    }
}
fn main() {}""",
        }

    @patch('asyncio.create_subprocess_exec')
    async def test_verification_error_patterns(self, mock_subprocess, common_error_patterns):
        """Test that common error patterns are detected"""
        for error_type, code in common_error_patterns.items():
            # Mock the subprocess
            mock_process = Mock()
            mock_process.returncode = 1
            mock_process.communicate.return_value = (b"", f"verification error in {error_type}".encode())
            mock_subprocess.return_value = mock_process
            
            success, output, error = await verify_verus_code(code)
            assert not success, f"Expected {error_type} to fail verification"
            assert error_type in error
