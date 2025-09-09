"""Git operations and URL generation utilities."""

from pathlib import Path
from typing import Optional
from urllib.parse import quote

import git
from git.exc import GitCommandError, InvalidGitRepositoryError


def get_git_remote_url() -> str | None:
    """Get the GitHub remote URL from git configuration."""
    try:
        repo = git.Repo(search_parent_directories=True)
        if "origin" not in repo.remotes:
            print("Error: No 'origin' remote found.")
            return None

        remote_url = repo.remotes.origin.url
        if remote_url.startswith("git@github.com:"):
            remote_url = remote_url.replace(
                "git@github.com:", "https://github.com/"
            ).replace(".git", "")
        elif remote_url.startswith("https://github.com/"):
            remote_url = remote_url.replace(".git", "")
        else:
            print(f"Warning: Unknown remote URL format: {remote_url}")
        return remote_url
    except InvalidGitRepositoryError:
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
        repo = git.Repo(search_parent_directories=True)
        return repo.active_branch.name
    except (InvalidGitRepositoryError, GitCommandError, TypeError):
        # TypeError can occur if repo.active_branch is None (detached HEAD)
        try:
            repo = git.Repo(search_parent_directories=True)
            # Try to get branch name from HEAD in detached state
            return repo.git.rev_parse("--abbrev-ref", "HEAD")
        except (InvalidGitRepositoryError, GitCommandError):
            return "main"


def get_github_url(file_path: Path, repo_url: str, branch: str = "main") -> str:
    """Generate GitHub URL for a file."""
    repo_url = repo_url.rstrip("/")
    encoded_path = quote(str(file_path))
    github_url = f"{repo_url}/blob/{branch}/{encoded_path}"
    return github_url


def get_repo_root(start: Optional[Path] = None) -> Path:
    """Find the repository root.

    - If ``start`` is provided, search from that path upward for a Git repo.
    - Otherwise, search from the current working directory.
    - Falls back to scanning for a ``.git`` directory upward.
    """
    base = start if start is not None else Path.cwd()
    try:
        # GitPython can search from an explicit path
        repo = git.Repo(base, search_parent_directories=True)
        return Path(repo.working_dir)
    except InvalidGitRepositoryError:
        # Fallback to manual search upward from the provided base
        current = base
        while current != current.parent:
            if (current / ".git").exists():
                return current
            current = current.parent
        # Last resort: return the current working directory
        return Path.cwd()
