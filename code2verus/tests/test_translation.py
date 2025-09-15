"""Test core translation functionality"""

import pytest
from unittest.mock import Mock, patch, AsyncMock

from code2verus.agent import translate_code_to_verus, create_agent


@pytest.fixture
def mock_agent():
    """Create a mock agent for testing"""
    agent = Mock()
    agent.run_sync = Mock()
    return agent


@pytest.fixture
def sample_dafny_code():
    """Sample Dafny code for testing"""
    return """
function method add(x: int, y: int): int
{
    x + y
}

method testAdd()
{
    assert add(2, 3) == 5;
}
"""


@pytest.fixture
def sample_lean_code():
    """Sample Lean code for testing"""
    return """
def add (x y : Int) : Int := x + y

theorem add_comm (x y : Int) : add x y = add y x := by
  simp [add]
  ring
"""


@pytest.fixture
def sample_verus_output():
    """Expected Verus output for testing"""
    return """use vstd::prelude::*;

verus! {
    spec fn add(x: int, y: int) -> int {
        x + y
    }

    fn test_add() {
        assert(add(2, 3) == 5);
    }
}

fn main() {}"""


class TestTranslation:
    """Test translation functionality"""

    def test_create_agent(self):
        """Test agent creation"""
        agent = create_agent("dafny")
        assert agent is not None

        agent = create_agent("lean")
        assert agent is not None

    @patch("code2verus.agent.create_agent")
    async def test_translate_dafny_to_verus_success(
        self, mock_create_agent, sample_dafny_code, sample_verus_output
    ):
        """Test successful Dafny to Verus translation"""
        # Setup mock
        mock_agent = AsyncMock()
        mock_result = Mock()
        mock_result.output = sample_verus_output
        mock_result.all_messages = Mock(return_value=[])  # Empty conversation history
        mock_agent.run = AsyncMock(return_value=mock_result)
        mock_create_agent.return_value = mock_agent

        # Test translation
        result = await translate_code_to_verus(
            source_code=sample_dafny_code, source_language="dafny", max_iterations=1
        )

        # Check that we get a TranslationResult with the expected output
        assert result.output_content == sample_verus_output
        assert result.num_iterations == 1
        assert (
            result.code_for_verification == sample_verus_output
        )  # For non-YAML, these are the same
        mock_agent.run.assert_called_once()

    @patch("code2verus.agent.create_agent")
    async def test_translate_lean_to_verus_success(
        self, mock_create_agent, sample_lean_code, sample_verus_output
    ):
        """Test successful Lean to Verus translation"""
        # Setup mock
        mock_agent = AsyncMock()
        mock_result = Mock()
        mock_result.output = sample_verus_output
        mock_result.all_messages = Mock(return_value=[])  # Empty conversation history
        mock_agent.run = AsyncMock(return_value=mock_result)
        mock_create_agent.return_value = mock_agent

        # Test translation
        result = await translate_code_to_verus(
            source_code=sample_lean_code, source_language="lean", max_iterations=1
        )

        # Check that we get a TranslationResult with the expected output
        assert result.output_content == sample_verus_output
        assert result.num_iterations == 1
        assert (
            result.code_for_verification == sample_verus_output
        )  # For non-YAML, these are the same
        mock_agent.run.assert_called_once()

    @patch("code2verus.agent.create_agent")
    async def test_translate_with_retries(self, mock_create_agent, sample_dafny_code):
        """Test translation with retries on failure"""
        mock_agent = AsyncMock()
        # First call fails, second succeeds
        success_result = Mock()
        success_result.output = (
            "use vstd::prelude::*;\nverus! { fn test() {} }\nfn main() {}"
        )
        success_result.all_messages = Mock(return_value=[])
        mock_agent.run = AsyncMock(side_effect=[Exception("API error"), success_result])
        mock_create_agent.return_value = mock_agent

        result = await translate_code_to_verus(
            source_code=sample_dafny_code, source_language="dafny", max_iterations=3
        )

        assert "use vstd::prelude::*;" in result.output_content
        assert mock_agent.run.call_count == 2

    @patch("code2verus.agent.create_agent")
    async def test_translate_max_iterations_exceeded(
        self, mock_create_agent, sample_dafny_code
    ):
        """Test translation failure when max iterations exceeded"""
        mock_agent = AsyncMock()
        mock_agent.run = AsyncMock(side_effect=Exception("API error"))
        mock_create_agent.return_value = mock_agent

        with pytest.raises(Exception, match="API error"):
            await translate_code_to_verus(
                source_code=sample_dafny_code, source_language="dafny", max_iterations=2
            )

        assert mock_agent.run.call_count == 2

    def test_unsupported_language(self):
        """Test error handling for unsupported languages"""
        with pytest.raises(ValueError):
            create_agent("unsupported_language")


class TestYAMLTranslation:
    """Test YAML-specific translation functionality"""

    @pytest.fixture
    def sample_dafny_yaml(self):
        """Sample Dafny YAML input"""
        return {
            "vc-description": "Test function",
            "vc-preamble": "// Dafny preamble",
            "vc-helpers": "// helpers",
            "vc-signature": "function add(x: int, y: int): int",
            "vc-implementation": "x + y",
            "vc-condition": "ensures add(x, y) == x + y",
            "vc-proof": "// proof here",
            "vc-postamble": "// end",
        }

    @pytest.fixture
    def sample_lean_yaml(self):
        """Sample Lean YAML input"""
        return {
            "vc-description": "/- Test function -/",
            "vc-preamble": "import Mathlib",
            "vc-helpers": "-- helpers",
            "vc-signature": "def add (x y : Int) : Int :=",
            "vc-implementation": "x + y",
            "vc-condition": "theorem add_spec : add x y = x + y := by",
            "vc-proof": "simp [add]",
            "vc-postamble": "-- end",
        }

    @patch("code2verus.agent.create_agent")
    async def test_yaml_translation_field_mapping(
        self, mock_create_agent, sample_lean_yaml
    ):
        """Test that YAML field mapping works correctly"""
        expected_verus_yaml = """vc-description: |-
  Test function
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

        mock_agent = AsyncMock()
        mock_result = Mock()
        mock_result.output = expected_verus_yaml
        mock_result.all_messages = Mock(return_value=[])
        mock_agent.run = AsyncMock(return_value=mock_result)
        mock_create_agent.return_value = mock_agent

        import yaml

        yaml_content = yaml.dump(sample_lean_yaml, default_flow_style=False)

        result = await translate_code_to_verus(
            source_code=yaml_content, source_language="lean", max_iterations=1
        )

        # Verify expected YAML structure is present
        assert "vc-spec:" in result.output_content
        assert "vc-code:" in result.output_content
        assert "assume(false)" in result.output_content
        assert "use vstd::prelude::*;" in result.output_content

    def test_yaml_forbidden_fields_removed(self, sample_dafny_yaml):
        """Test that forbidden YAML fields are properly identified"""
        from code2verus.config import cfg

        forbidden_fields = cfg["forbidden_yaml_fields"]

        # Check that the expected forbidden fields are configured
        assert "vc-implementation" in forbidden_fields
        assert "vc-signature" in forbidden_fields
        assert "vc-condition" in forbidden_fields
        assert "vc-proof" in forbidden_fields

        # These should be present in output
        input_fields = set(sample_dafny_yaml.keys())
        forbidden_set = set(forbidden_fields)

        # Verify our test data has the forbidden fields
        assert forbidden_set.intersection(input_fields) == forbidden_set


class TestErrorHandling:
    """Test error handling in translation"""

    @patch("code2verus.agent.create_agent")
    async def test_empty_code_translation(self, mock_create_agent):
        """Test translation of empty code"""
        mock_agent = AsyncMock()
        mock_result = Mock()
        mock_result.output = "// Empty translation"
        mock_result.all_messages = Mock(return_value=[])
        mock_agent.run = AsyncMock(return_value=mock_result)
        mock_create_agent.return_value = mock_agent

        result = await translate_code_to_verus(
            source_code="", source_language="dafny", max_iterations=1
        )

        assert isinstance(result.output_content, str)

    @patch("code2verus.agent.create_agent")
    async def test_malformed_source_code(self, mock_create_agent):
        """Test handling of malformed source code"""
        mock_agent = AsyncMock()
        mock_result = Mock()
        mock_result.output = "// Error translation"
        mock_result.all_messages = Mock(return_value=[])
        mock_agent.run = AsyncMock(return_value=mock_result)
        mock_create_agent.return_value = mock_agent

        malformed_code = "this is not valid dafny $$$ %%% @@@"

        result = await translate_code_to_verus(
            source_code=malformed_code, source_language="dafny", max_iterations=1
        )

        assert isinstance(result.output_content, str)
