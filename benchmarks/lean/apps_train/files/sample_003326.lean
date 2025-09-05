In the wake of the npm's `left-pad` debacle, you decide to write a new super padding method that superceds the functionality of `left-pad`. Your version will provide the same functionality, but will additionally add right, and justified padding of string -- the `super_pad`.

Your function `super_pad` should take three arguments: the string `string`, the width of the final string `width`, and a fill character `fill`. However, the fill character can be enriched with a format string resulting in different padding strategies. If `fill` begins with `'<'` the string is padded on the left with the remaining fill string and if `fill` begins with `'>'` the string is padded on the right. Finally, if `fill` begins with `'^'` the string is padded on the left and the right, where the left padding is always greater or equal to the right padding. The `fill` string can contain more than a single char, of course. 

Some examples to clarify the inner workings:

- `super_pad("test", 10)` returns "      test"
- `super_pad("test", 10, "x")` returns `"xxxxxxtest"`
- `super_pad("test", 10, "xO")` returns `"xOxOxOtest"`
- `super_pad("test", 10, "xO-")` returns `"xO-xO-test"`
- `super_pad("some other test", 10, "nope")` returns `"other test"`
- `super_pad("some other test", 10, "> ")` returns `"some other"`
- `super_pad("test", 7, ">nope")` returns `"testnop"`
- `super_pad("test", 7, "^more complex")` returns `"motestm"`
- `super_pad("test", 7, "")` returns `"test"`

The `super_pad` method always returns a string of length `width` if possible. We expect the `width` to be positive (including 0) and the fill could be also an empty string.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded