The Padovan sequence is the sequence of integers `P(n)` defined by the initial values

`P(0)=P(1)=P(2)=1`

and the recurrence relation

`P(n)=P(n-2)+P(n-3)`

The first few values of `P(n)` are

`1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 12, 16, 21, 28, 37, 49, 65, 86, 114, 151, 200, 265, ...`

### Task 

The task is to write a method that returns i-th Padovan number

```python
> padovan(0) == 1
> padovan(1) == 1
> padovan(2) == 1
> padovan(n) = padovan(n-2) + padovan(n-3)
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
