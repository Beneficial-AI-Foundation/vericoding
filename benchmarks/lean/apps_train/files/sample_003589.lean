You should have done Product Partitions I to do this second part.
If you solved it, you should have notice that we try to obtain the multiplicative partitions with ```n ≤ 100 ```.

In this kata we will have more challenging values, our ```n ≤  10000```. So, we need a more optimized a faster code.

We need the function ```prod_int_partII()``` that will give all the amount of different products, excepting the number itself multiplied by one.

The function ```prod_int_partII()``` will receive two arguments, the number ```n``` for the one we have to obtain all the multiplicative partitions, and an integer s that determines the products that have an amount of factors equals to ```s```.

The function will output a list with this structure:
```python
[(1), (2), [(3)]]

(1) Total amount of different products we can obtain, using the factors of n. (We do not consider the product n . 1)

(2) Total amount of products that have an amount of factors equals to s.

[(3)] A list of lists with each product represented with by a sorted list of the factors. All the product- lists should be sorted also.
If we have only one product-list as a result, the function will give only the list 
and will not use the list of lists
```
Let's see some cases:
```python
prod_int_partII(36, 3) == [8, 3, [[2, 2, 9], [2, 3, 6], [3, 3, 4]]]

/// (1) ----> 8 # Amount of different products, they are: [2, 2, 3, 3], [2, 2, 9], 
[2, 3, 6], [2, 18], [3, 3, 4], [3, 12], [4, 9], [6, 6] (8 products)

    (2) ----> 3 # Amount of products with three factors (see them bellow)

    (3) ----> [[2, 2, 9], [2, 3, 6], [3, 3, 4]] # These are the products with 3 factors
```
```python
prod_int_partII(48, 5) == [11, 1, [2, 2, 2, 2, 3]] # Only one list.
```
Again consider that some numbers will not have multiplicative partitions.
```python
prod_int_partII(37, 2) == [0, 0, []]
```
Happy coding!!

(Recursion is advisable)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
