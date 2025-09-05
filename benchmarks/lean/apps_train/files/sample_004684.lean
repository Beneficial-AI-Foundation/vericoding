# Is the string uppercase?

## Task

```if-not:haskell,csharp,javascript,coffeescript,elixir,forth,go,dart,julia,cpp,reason,typescript,racket,ruby
Create a method `is_uppercase()` to see whether the string is ALL CAPS. For example:
```
```if:haskell,reason,typescript
Create a method `isUpperCase` to see whether the string is ALL CAPS. For example:
```
```if:csharp
Create an extension method `IsUpperCase` to see whether the string is ALL CAPS. For example:
```
```if:julia
Create a function `isupper` to see whether the string is ALL CAPS. For example:
```
```if:cpp
Create a function `is_uppercase()` to see whether the string is ALL CAPS. For example:
```
```if:javascript,coffeescript
Add the `isUpperCase` method to `String` to see whether the string is ALL CAPS. For example:
```
```if:elixir
Create a method `upper_case?` to see whether the string is ALL CAPS. For example:
```
```if:forth,factor
Create a word `uppercase?` to check whether a string is ALL CAPS. For example:
```
```if:go
Create a method `IsUpperCase` to see whether the string is ALL CAPS. For example:
```
```if:racket
Create a method `upcase?` to see whether the string is ALL CAPS. For example:
```
```if:ruby
Create a method `is_upcase?` to see whether the string is ALL CAPS. For example:
```

```python
is_uppercase("c") == False
is_uppercase("C") == True
is_uppercase("hello I AM DONALD") == False
is_uppercase("HELLO I AM DONALD") == True
is_uppercase("ACSKLDFJSgSKLDFJSKLDFJ") == False
is_uppercase("ACSKLDFJSGSKLDFJSKLDFJ") == True
```

In this Kata, a string is said to be in ALL CAPS whenever it does not contain any lowercase letter so any string containing no letters at all is trivially considered to be in ALL CAPS.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded