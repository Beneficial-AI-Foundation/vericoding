### Task

Your main goal is to find two numbers(` >= 0 `), greatest common divisor of wich will be `divisor` and number of iterations, taken by Euclids algorithm will be `iterations`.

### Euclid's GCD

```CSharp
BigInteger FindGCD(BigInteger a, BigInteger b) {
  // Swaping `a` and `b`
  if (a < b) {
    a += b;
    b = a - b;
    a = a - b;
  }

  while (b > 0) {
    // Iteration of calculation
    BigInteger c = a % b;
    a = b;
    b = c;
  }

  // `a` - is greates common divisor now
  return a;
}
```

### Restrictions

Your program should work with numbers

`0 < divisor < 1000`

`0 <= iterations <= 50'000`

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
