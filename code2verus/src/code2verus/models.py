from pydantic import BaseModel, Field
from datetime import datetime
from typing import List, Optional, Dict, Any
from enum import Enum
import uuid


class IterationStatus(str, Enum):
    PENDING = "pending"
    RUNNING = "running"
    SUCCESS = "success"
    FAILED = "failed"
    YAML_ERROR = "yaml_error"
    VERIFICATION_ERROR = "verification_error"


class ConversationExchange(BaseModel):
    iteration: int
    prompt: str
    response: str
    prompt_length: int
    response_length: int
    message_history_length: int
    timestamp: datetime = Field(default_factory=datetime.now)


class VerificationError(BaseModel):
    iteration: int
    error: str
    output: Optional[str] = None
    error_type: str = "verification"
    timestamp: datetime = Field(default_factory=datetime.now)


class AttemptResult(BaseModel):
    iteration: int
    output_content: str
    verification_success: bool
    verification_error: Optional[str] = None
    status: IterationStatus
    timestamp: datetime = Field(default_factory=datetime.now)


class TranslationDebugContext(BaseModel):
    """Structured debug context for translation operations with type safety and validation"""

    # Immutable context
    original_source: str
    source_language: str
    is_yaml: bool
    max_iterations: int
    session_id: str = Field(default_factory=lambda: str(uuid.uuid4()))
    start_time: datetime = Field(default_factory=datetime.now)

    # Mutable state
    current_iteration: int = 0
    previous_attempts: List[AttemptResult] = Field(default_factory=list)
    verification_errors: List[VerificationError] = Field(default_factory=list)
    conversation_exchanges: List[ConversationExchange] = Field(default_factory=list)

    # Enhanced timing tracking
    end_time: Optional[datetime] = None
    last_activity: datetime = Field(default_factory=datetime.now)

    # Helper methods for easier access and manipulation
    def add_attempt(self, attempt: AttemptResult) -> None:
        """Add a new attempt result to the context"""
        self.previous_attempts.append(attempt)
        self.last_activity = datetime.now()

    def add_verification_error(self, error: VerificationError) -> None:
        """Add a new verification error to the context"""
        self.verification_errors.append(error)
        self.last_activity = datetime.now()

    def add_conversation_exchange(self, exchange: ConversationExchange) -> None:
        """Add a new conversation exchange to the context"""
        self.conversation_exchanges.append(exchange)
        self.last_activity = datetime.now()

    def get_latest_error(self) -> Optional[VerificationError]:
        """Get the most recent verification error, if any"""
        return self.verification_errors[-1] if self.verification_errors else None

    def get_latest_attempt(self) -> Optional[AttemptResult]:
        """Get the most recent attempt result, if any"""
        return self.previous_attempts[-1] if self.previous_attempts else None

    def increment_iteration(self) -> None:
        """Increment the current iteration counter"""
        self.current_iteration += 1
        self.last_activity = datetime.now()

    def mark_completed(self) -> None:
        """Mark the session as completed"""
        self.end_time = datetime.now()
        self.last_activity = self.end_time

    def get_duration(self) -> float:
        """Get the duration of the session in seconds"""
        end = self.end_time or datetime.now()
        return (end - self.start_time).total_seconds()

    def get_formatted_timestamps(self) -> Dict[str, str]:
        """Get human-readable formatted timestamps"""
        return {
            "start_time": self.start_time.strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "end_time": self.end_time.strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
            if self.end_time
            else "ongoing",
            "last_activity": self.last_activity.strftime("%Y-%m-%d %H:%M:%S.%f")[:-3],
            "duration": f"{self.get_duration():.3f} seconds",
        }

    def to_summary_dict(self) -> Dict[str, Any]:
        """Generate a summary dictionary for logging purposes"""
        end_time = datetime.now()
        duration = (end_time - self.start_time).total_seconds()

        return {
            "session_id": self.session_id,
            "duration_seconds": duration,
            "source_language": self.source_language,
            "is_yaml": self.is_yaml,
            "max_iterations": self.max_iterations,
            "current_iteration": self.current_iteration,
            "total_attempts": len(self.previous_attempts),
            "total_errors": len(self.verification_errors),
            "total_exchanges": len(self.conversation_exchanges),
            "success": len(self.previous_attempts) > 0
            and self.previous_attempts[-1].verification_success,
            "final_status": self.get_final_status(),
            "source_code_length": len(self.original_source),
            # Enhanced timing information
            "timestamps": self.get_formatted_timestamps(),
            "session_completed": self.end_time is not None,
        }

    def get_final_status(self) -> str:
        """Determine the final status of the translation process"""
        if not self.previous_attempts:
            return "no_attempts"

        latest_attempt = self.previous_attempts[-1]
        if latest_attempt.verification_success:
            return "success"
        elif (
            self.verification_errors
            and self.verification_errors[-1].error_type == "yaml_syntax"
        ):
            return "yaml_error"
        else:
            return "verification_failed"


class VerusToolResult(BaseModel):
    success: bool
    output: str
    error: str = ""


class DafnyToolResult(BaseModel):
    success: bool
    output: str
    error: str = ""
