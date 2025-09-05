In your class, you have started lessons about [arithmetic progression](https://en.wikipedia.org/wiki/Arithmetic_progression). Since you are also a programmer, you have decided to write a function that will return the first `n` elements of the sequence with the given common difference `d` and first element `a`. Note that the difference may be zero!

The result should be a string of numbers, separated by comma and space.

## Example

```python
# first element: 1, difference: 2, how many: 5
arithmetic_sequence_elements(1, 2, 5) == "1, 3, 5, 7, 9"
```

~~~if:fortran
*NOTE: In Fortran, your returned string is* **not** *permitted to contain redundant leading/trailing whitespace.*
~~~

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
