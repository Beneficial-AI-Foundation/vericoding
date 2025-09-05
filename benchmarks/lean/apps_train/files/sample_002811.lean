You are given an input string.

For each symbol in the string if it's the first character occurrence, replace it with a '1', else replace it with the amount of times you've already seen it...

But will your code be **performant enough**?

___

## Examples:

```
input   =  "Hello, World!"
result  =  "1112111121311"

input   =  "aaaaaaaaaaaa"
result  =  "123456789101112"
```

There might be some non-ascii characters in the string.

~~~if:java
Note: there will be no int domain overflow (character occurrences will be less than 2 billion).
~~~
~~~if:c
(this does not apply to the C language translation)
~~~

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
