Imagine if there were no order of operations. Instead, you would do the problem from left to right. For example, the equation `$a +b  *c /d$` would become `$(((a+b)*c)//d)$` (`Math.floor(((a+b)*c)/d)` in JS). Return `None`/`null` (depending on your language) if the equation is `""`.

### Task:

Given an equation with a random amount of spaces greater than or equal to zero between each number and operation, return the result without order of operations. Note that if two numbers are spaces apart, act as if they were one number: `1   3` = `13`. However, if given something `% 0` or something `/ 0`, return `None/null`.

More about order of operations: [here](https://en.wikipedia.org/wiki/Order_of_operations#:~:text=In%20the%20United%20States%2C%20the,Excuse%20My%20Dear%20Aunt%20Sally%22.)

### Key:

- `^` represents `**`

```if:python
- `/` represents `//` or `math.floor` because the result will always be an integer
```

```if:javascript
- `/` should always be rounded down(`Math.floor`) because the result will always be an integer
```

### Operations allowed: 
 `+, -, * , /, ^, %`

### Example:

`no_order(2 + 3 - 4 * 1 ^ 3) returns 1`

because:
```
  2 + 3 - 4 * 1 ^ 3
= 2 + 3 - 4 * 1 ^ 3
= 5 - 4 * 1 ^ 3
= 1 * 1 ^ 3
= 1 ^ 3
= 1
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded