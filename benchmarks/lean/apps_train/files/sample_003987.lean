# Task
 Dudka has `n` details. He must keep exactly 3 of them.

 To do this, he performs the following operations until he has only 3 details left:
```
He numbers them.
He keeps those with either odd or even numbers and throws the others away.```

 Dudka wants to know how many ways there are to get exactly 3 details. Your task is  to help him calculate it.

# Example

 For `n = 6`, the output should be `2`.
 ```
Dudka has 6 details, numbered 1 2 3 4 5 6. 
He can keep either details with numbers 1, 3, 5, 
or with numbers 2, 4, 6. 
Both options leave him with 3 details, 
so the answer is 2.```

 For `n = 7`, the output should be `1`.
 ```
Dudka has 7 details, numbered 1 2 3 4 5 6 7. 
He can keep either details 1 3 5 7, or details 2 4 6. 
If he keeps details 1 3 5 7 , 
he won't be able to get 3 details in the future, 
because at the next step he will number them 1 2 3 4 
and will have to keep either details 1 3, or 2 4, 
only two details anyway. 
That's why he must keep details 2 4 6 at the first step, 
so the answer is 1.```

# Input/Output

 - `[input]` integer `n`

  `3 ≤ n ≤ 10^9`

 - `[output]` an integer

  The number of ways to get exactly 3 details.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded