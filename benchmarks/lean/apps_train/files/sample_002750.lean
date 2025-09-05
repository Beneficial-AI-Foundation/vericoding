Bob has ladder. He wants to climb this ladder, but being a precocious child, he wonders about exactly how many ways he could to climb this `n` size ladder using jumps of up to distance `k`.

Consider this example...

n = 5\
k = 3

Here, Bob has ladder of length 5, and with each jump, he can ascend up to 3 steps (he can either jump step 1 or 2 or 3). This gives the below possibilities

```
1 1 1 1 1
1 1 1 2
1 1 2 1 
1 2 1 1
2 1 1 1
1 2 2
2 2 1
2 1 2
1 1 3
1 3 1
3 1 1
2 3
3 2
```

Your task to calculate number of ways to climb ladder of length `n` with upto `k` steps for Bob. (13 in above case)

Constraints:

```python
1<=n<=50
1<=k<=15
```

_Tip: try fibonacci._

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded