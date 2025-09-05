Karan's company makes software that provides different features based on the version of operating system of the user.

For finding which version is more recent, Karan uses the following method:

While this function worked for OS versions 10.6, 10.7, 10.8 and 10.9, the Operating system company just released OS version 10.10.

Karan's function fails for the new version:

```python
compare_versions ("10.9", "10.10");       # returns True, while it should return False
```

Karan now wants to spend some time to right a more robust version comparison function that works for any future version/sub-version updates.

Help Karan write this function. Here are a few sample cases:

```python
compare_versions("11", "10");                    # returns True
compare_versions("11", "11");                    # returns True
compare_versions("10.4.6", "10.4");              # returns True
compare_versions("10.4", "11");                  # returns False
compare_versions("10.4", "10.10");               # returns False
compare_versions("10.4.9", "10.5");              # returns False
```
```haskell  
compareVersions "11" "10"       `shouldBe` GT
compareVersions "10.4.6" "10.4" `shouldBe` GT
compareVersions "10.10" "10.9"  `shouldBe` GT
compareVersions xs xs           `shouldBe` EQ -- xs is an arbitrary version
compareVersions "10" "11"         `shouldBe` LT
compareVersions "10.4" "10.4.6"   `shouldBe` LT
compareVersions "10.99" "10.100"  `shouldBe` LT
```

It can be assumed that version strings are non empty and only contain numeric literals and the character `'.'`.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded