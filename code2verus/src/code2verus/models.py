from pydantic import BaseModel


class VerusToolResult(BaseModel):
    success: bool
    output: str
    error: str = ""


class DafnyToolResult(BaseModel):
    success: bool
    output: str
    error: str = ""
