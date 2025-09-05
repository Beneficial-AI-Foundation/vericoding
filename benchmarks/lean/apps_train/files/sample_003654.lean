You are given three integers in the range [0-99]. You must determine if any ordering of the numbers forms a date from the 20th century.

- If no ordering forms a date, return the string `"invalid"`.

- If multiple distinct orderings form dates, return the string `"ambiguous"`.

- If only one ordering forms a date, return that date as a string with format `"YY/MM/DD"`.

## Examples

```python
unique_date(13, 12, 77) == '77/12/13' # only the ordering (77, 12, 13) forms a date
unique_date(13, 77, 12) == '77/12/13' # argument order is irrelevant

unique_date(1, 2, 3) == 'ambiguous' # 01/02/03, 02/01/03, ...
unique_date(3, 2, 1) == 'ambiguous'

unique_date(50, 40, 60) == 'invalid' # no ordering could form a date
unique_date(40, 50, 60) == 'invalid'
```

## Note
This kata was inspired by my encounter with [google.com/foobar](http://www.google.com/foobar)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded