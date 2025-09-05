In this kata, you will make a function that converts between `camelCase`, `snake_case`, and `kebab-case`.

You must write a function that changes to a given case. It must be able to handle all three case types:

```python
py> change_case("snakeCase", "snake")
"snake_case"
py> change_case("some-lisp-name", "camel")
"someLispName"
py> change_case("map_to_all", "kebab")
"map-to-all"
py> change_case("doHTMLRequest", "kebab")
"do-h-t-m-l-request"
py> change_case("invalid-inPut_bad", "kebab")
None
py> change_case("valid-input", "huh???")
None
py> change_case("", "camel")
""
```

Your function must deal with invalid input as shown, though it will only be passed strings. Furthermore, all valid identifiers will be lowercase except when necessary, in other words on word boundaries in `camelCase`.

_**(Any translations would be greatly appreciated!)**_

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded