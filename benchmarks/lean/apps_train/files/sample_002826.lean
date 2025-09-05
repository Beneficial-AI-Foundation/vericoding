Given a natural number n, we want to know in how many ways we may express these numbers as product of other numbers.

For example the number
```python
 18 = 2 x 9 = 3 x 6 = 2 x 3 x 3 # (we do not consider the product 18 x 1), (3 ways) 
```

See this example a bit more complicated,
```python
60 = 2 x 30 = 3 x 20 =  4 x 15 = 5 x 12 = 6 x 10 = 2 x 2 x 15 = 2 x 3 x 10 = 2 x 5 x 6 =  3 x 4 x 5 = 2 x 2 x 3 x 5 (10 ways)
```
We need the function ```prod_int_part()```, that receives a number n, and ouputs the amount of total different products with all the products of max length sorted in this way:

1) each product will be expressed in a list of its factors in incresing order from left to right

2) if there is more than one list-product, these lists should be ordered by the value of the first term, if two lists have the same term equal thay should be ordered by the value of the second term.

Let's see some cases:
```python
prod_int_part(18) == [3, [2, 3, 3]]

prod_int_part(60) == [10, [2, 2, 3, 5]
```

If we have only one list-product with the maximum length, there is no use to have it with two nested braces, so the result will be like this case:
```python
prod_int_part(54) == [6, [2, 3, 3, 3]]
```

Now, let's see examples when ```n``` cannot be partitioned:
```python
prod_int_part(37) == [0, []]

prod_int_part(61) == [0, []]
```
Enjoy it!!

def prod_int_part (n: Nat) (min: Nat := 2) : Nat × List Nat := sorry

theorem prod_int_part_output_structure (n: Nat) (h: n ≥ 2) : 
  let result := prod_int_part n
  result.1 ≥ 0 ∧ result.2.all (λ x => x ≥ 2) := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
