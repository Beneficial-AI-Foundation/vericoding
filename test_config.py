#!/usr/bin/env python3

import tomllib
from pathlib import Path

def test_config():
    config_path = Path("config/language_config.toml")
    print(f"Config path exists: {config_path.exists()}")
    
    with config_path.open("rb") as f:
        config = tomllib.load(f)
    
    print("Config keys:", list(config.keys()))
    
    for lang, settings in config.items():
        if lang != "common":
            print(f"\nLanguage: {lang}")
            print(f"Settings keys: {list(settings.keys())}")
            if "name" in settings:
                print(f"Name: {settings['name']}")
            else:
                print("No 'name' key found!")

if __name__ == "__main__":
    test_config() 