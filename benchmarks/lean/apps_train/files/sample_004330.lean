Assume `"#"` is like a backspace in string. This means that string `"a#bc#d"` actually is `"bd"`

Your task is to process a string with `"#"` symbols.

## Examples

```
"abc#d##c"      ==>  "ac"
"abc##d######"  ==>  ""
"#######"       ==>  ""
""              ==>  ""
```

def clean_string (s : String) : String := sorry

theorem clean_string_idempotent (s : String) :
  clean_string (clean_string s) = clean_string s := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
