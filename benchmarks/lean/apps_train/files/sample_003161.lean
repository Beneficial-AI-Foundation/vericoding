In this kata, you will be given a string of text and valid parentheses, such as `"h(el)lo"`. You must return the string, with only the text inside parentheses reversed, so `"h(el)lo"` becomes `"h(le)lo"`. However, if said parenthesized text contains parenthesized text itself, then that too must reversed back, so it faces the original direction. When parentheses are reversed, they should switch directions, so they remain syntactically correct (i.e. `"h((el)l)o"` becomes `"h(l(el))o"`). This pattern should repeat for however many layers of parentheses. There may be multiple groups of parentheses at any level (i.e. `"(1) (2 (3) (4))"`), so be sure to account for these.

For example:
```python
reverse_in_parentheses("h(el)lo") == "h(le)lo"
reverse_in_parentheses("a ((d e) c b)") == "a (b c (d e))"
reverse_in_parentheses("one (two (three) four)") == "one (ruof (three) owt)"
reverse_in_parentheses("one (ruof ((rht)ee) owt)") == "one (two ((thr)ee) four)"
```

Input parentheses will always be valid (i.e. you will never get "(()").

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded