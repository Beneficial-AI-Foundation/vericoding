"""Tests for wandb logger - verifies actual behavior, not theater."""

import os
import pytest
from unittest.mock import Mock, patch, MagicMock
from vericoding.utils.wandb_logger import WandbLogger, get_wandb_logger


class TestWandbLogger:
    """Test wandb logger functionality."""
    
    def test_disabled_without_api_key(self):
        """Logger should be disabled without API key."""
        with patch.dict(os.environ, {}, clear=True):
            logger = WandbLogger()
            assert not logger.enabled
            assert logger.init_run() is None
    
    def test_disabled_with_mode_disabled(self):
        """Logger respects WANDB_MODE=disabled."""
        with patch.dict(os.environ, {"WANDB_MODE": "disabled", "WANDB_API_KEY": "test"}):
            logger = WandbLogger()
            assert not logger.enabled
    
    @patch("wandb.init")
    def test_init_run_handles_failure(self, mock_init):
        """Init should handle wandb failures gracefully."""
        mock_init.side_effect = Exception("Network error")
        
        with patch.dict(os.environ, {"WANDB_API_KEY": "test"}):
            logger = WandbLogger()
            result = logger.init_run(name="test")
            
            assert result is None
            assert not logger.enabled  # Should disable on failure
    
    @patch("wandb.init")
    @patch("wandb.log")
    def test_metrics_tracking(self, mock_log, mock_init):
        """Test actual metrics are logged correctly."""
        mock_run = MagicMock()
        mock_init.return_value = mock_run
        
        with patch.dict(os.environ, {"WANDB_API_KEY": "test"}):
            logger = WandbLogger()
            logger.init_run()
            
            # Test verification logging
            logger.log_verification(
                file_path="test.lean",
                iteration=1,
                success=False,
                error_text="Type mismatch at line 42"
            )
            
            # Verify correct metrics were logged
            mock_log.assert_called_once()
            logged_metrics = mock_log.call_args[0][0]
            assert "verify/test/iter" in logged_metrics
            assert "verify/test/success" in logged_metrics
            assert "errors/test/type_mismatch" in logged_metrics
            assert logged_metrics["verify/test/success"] == 0
    
    @patch("wandb.init")
    @patch("wandb.log")
    def test_cost_accumulation(self, mock_log, mock_init):
        """Test that costs are accumulated correctly."""
        mock_run = MagicMock()
        mock_init.return_value = mock_run
        
        with patch.dict(os.environ, {"WANDB_API_KEY": "test"}):
            logger = WandbLogger()
            logger.init_run()
            
            # Log multiple LLM calls
            logger.log_llm_call(model="gpt-4", latency_ms=1000, cost_usd=0.01)
            logger.log_llm_call(model="gpt-4", latency_ms=1500, cost_usd=0.02)
            
            # Check second call has accumulated cost
            second_call_metrics = mock_log.call_args_list[1][0][0]
            assert second_call_metrics["llm/total_cost"] == 0.03
    
    def test_singleton_pattern(self):
        """Test that get_wandb_logger returns same instance."""
        logger1 = get_wandb_logger()
        logger2 = get_wandb_logger()
        assert logger1 is logger2
    
    @patch("wandb.init")
    def test_error_pattern_detection(self, mock_init):
        """Test that error patterns are correctly detected."""
        mock_run = MagicMock()
        mock_init.return_value = mock_run
        
        with patch.dict(os.environ, {"WANDB_API_KEY": "test"}):
            with patch("wandb.log") as mock_log:
                logger = WandbLogger()
                logger.init_run()
                
                # Test different error patterns
                test_cases = [
                    ("Type mismatch in hypothesis", "errors/test/type_mismatch"),
                    ("Proof contains sorry", "errors/test/incomplete_proof"),
                    ("Verification timeout after 30s", "errors/test/timeout"),
                ]
                
                for error_text, expected_key in test_cases:
                    mock_log.reset_mock()
                    logger.log_verification(
                        file_path="test.lean",
                        iteration=1,
                        success=False,
                        error_text=error_text
                    )
                    
                    logged_metrics = mock_log.call_args[0][0]
                    assert expected_key in logged_metrics
                    assert logged_metrics[expected_key] == 1