"""Git operations and URL generation utilities."""

import subprocess
from pathlib import Path
from urllib.parse import quote


def get_git_remote_url() -> str | None:
    """Get the GitHub remote URL from git configuration."""
    try:
        result = subprocess.run(
            ["git", "config", "--get", "remote.origin.url"],
            capture_output=True,
            text=True,
            check=True,
        )
        remote_url = result.stdout.strip()
        if remote_url.startswith("git@github.com:"):
            remote_url = remote_url.replace(
                "git@github.com:", "https://github.com/"
            ).replace(".git", "")
        elif remote_url.startswith("https://github.com/"):
            remote_url = remote_url.replace(".git", "")
        else:
            print(f"Warning: Unknown remote URL format: {remote_url}")
        return remote_url
    except subprocess.CalledProcessError:
        print(
            "Error: Could not get git remote URL. Make sure you're in a git repository."
        )
        return None
    except Exception as e:
        print(f"Error getting git remote URL: {e}")
        return None


def get_current_branch() -> str:
    """Get the current git branch."""
    try:
        result = subprocess.run(
            ["git", "branch", "--show-current"],
            capture_output=True,
            text=True,
            check=True,
        )
        return result.stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        try:
            result = subprocess.run(
                ["git", "rev-parse", "--abbrev-ref", "HEAD"],
                capture_output=True,
                text=True,
                check=True,
            )
            return result.stdout.strip()
        except (subprocess.CalledProcessError, FileNotFoundError):
            return "main"


def get_github_url(file_path: Path, repo_url: str, branch: str = "main") -> str:
    """Generate GitHub URL for a file."""
    repo_url = repo_url.rstrip("/")
    encoded_path = quote(str(file_path))
    github_url = f"{repo_url}/blob/{branch}/{encoded_path}"
    return github_url


def get_repo_root() -> Path:
    """Find the repository root by looking for .git directory."""
    current = Path.cwd()
    while current != current.parent:
        if (current / ".git").exists():
            return current
        current = current.parent
    return Path.cwd()  # Fallback to current directory
