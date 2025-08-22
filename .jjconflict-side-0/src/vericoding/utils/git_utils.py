"""Git operations and URL generation utilities."""

from pathlib import Path
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


def get_repo_root() -> Path:
    """Find the repository root by looking for .git directory."""
    try:
        repo = git.Repo(search_parent_directories=True)
        return Path(repo.working_dir)
    except InvalidGitRepositoryError:
        # Fallback to manual search if not in a git repository
        current = Path.cwd()
        while current != current.parent:
            if (current / ".git").exists():
                return current
            current = current.parent
        return Path.cwd()  # Fallback to current directory
