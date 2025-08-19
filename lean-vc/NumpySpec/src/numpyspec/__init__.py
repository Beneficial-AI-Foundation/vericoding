
from pathlib import Path
from dotenv import load_dotenv

# Auto-load environment variables from a local .env if present
env_path = Path(__file__).resolve().parent.parent.parent / ".env"
if env_path.exists():
    load_dotenv(dotenv_path=env_path)


def main() -> None:
    print("Hello from numpyspec!")
