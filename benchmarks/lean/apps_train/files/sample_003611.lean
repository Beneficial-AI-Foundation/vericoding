# Task:

We define the "self reversed power sequence" as one shown below:

Implement a function that takes 2 arguments (`ord max` and `num dig`), and finds the smallest term of the sequence whose index is less than or equal to `ord max`, and has exactly `num dig` number of digits.

If there is a number with correct amount of digits, the result should be an array in the form:

```python
[True, smallest found term]
[False, -1]
```

## Input range:

```python
ord_max <= 1000
```

___

## Examples:

```python
min_length_num(5, 10) == [True, 10]   # 10th term has 5 digits
min_length_num(7, 11) == [False, -1]  # no terms before the 13th one have 7 digits
min_length_num(7, 14) == [True, 13]   # 13th term is the first one which has 7 digits
```

Which you can see in the table below:

```
n-th Term    Term Value
1              0
2              1
3              3
4              8
5              22
6              65
7              209
8              732
9              2780
10             11377
11             49863
12             232768
13             1151914
14             6018785
```

___

Enjoy it and happy coding!!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
