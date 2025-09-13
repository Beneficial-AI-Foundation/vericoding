"""Preprocessing utilities for different languages."""


def ensure_mathlib_import(content: str) -> str:
    """
    Ensure Lean file has Mathlib import as the first line.
    
    Args:
        content: The original Lean file content
        
    Returns:
        The content with "import Mathlib" as the first line if it wasn't already present
    """
    if "import Mathlib" not in content:
        return "import Mathlib\n" + content
    return content


def preprocess_lean_file(content: str) -> str:
    """
    Preprocess Lean file content by wrapping each 'sorry' with vc-theorems tags.
    
    Args:
        content: The original Lean file content
        
    Returns:
        The preprocessed content with sorry statements wrapped in vc-theorems tags
        
    Raises:
        ValueError: If the content already contains <vc-theorems> tags
    """
    # Check if content already contains vc-theorems tags
    if "<vc-theorems>" in content:
        raise ValueError("File already contains <vc-theorems> tags - cannot preprocess")
    
    lines = content.split('\n')
    processed_lines = []
    
    for line in lines:
        # Check if this line contains 'sorry'
        if 'sorry' in line:
            # Add the opening tag before the line
            processed_lines.append('-- <vc-theorems>')
            processed_lines.append(line)
            # Add the closing tag after the line
            processed_lines.append('-- </vc-theorems>')
        else:
            processed_lines.append(line)
    
    return '\n'.join(processed_lines)