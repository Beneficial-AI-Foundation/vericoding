*This is the advanced version of the 
[Minimum and Maximum Product of k Elements](https://www.codewars.com/kata/minimum-and-maximum-product-of-k-elements/) kata.*

---

Given a list of **integers** and a positive integer `k` (> 0), find the minimum and maximum possible product of `k` elements taken from the list.

If you cannot take enough elements from the list, return `None`/`nil`.

## Examples

```python
numbers = [1, -2, -3, 4, 6, 7]

k = 1  ==>  -3, 7
k = 2  ==>  -21, 42    # -3*7, 6*7
k = 3  ==>  -126, 168  # -3*6*7, 4*6*7
k = 7  ==>  None       # there are only 6 elements in the list
```

Note: the test lists can contain up to 500 elements, so a naive approach will not work.

---

## My other katas

If you enjoyed this kata then please try [my other katas](https://www.codewars.com/collections/katas-created-by-anter69)! :-)

#### *Translations are welcome!*

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded