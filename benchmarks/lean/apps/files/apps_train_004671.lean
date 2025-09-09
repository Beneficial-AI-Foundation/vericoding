/-
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
-/

-- <vc-helpers>
-- </vc-helpers>

def gcd_iterations (a b : Int) : Int × Int := sorry

def find_initial_numbers (divisor iterations : Int) : Int × Int := sorry

theorem find_initial_numbers_positive (divisor iterations : Int)
  (h1 : divisor > 0) (h2 : iterations ≥ 0) :
  let (a, b) := find_initial_numbers divisor iterations
  a ≥ 0 ∧ b ≥ 0 := sorry

theorem find_initial_numbers_correct (divisor iterations : Int) 
  (h1 : divisor > 0) (h2 : iterations ≥ 0) :
  let (a, b) := find_initial_numbers divisor iterations
  let (gcd, iters) := gcd_iterations a b
  gcd = divisor ∧ iters = iterations := sorry

theorem find_initial_numbers_zero_case (divisor : Int)
  (h : divisor > 0) :
  let (a, b) := find_initial_numbers divisor 0
  b = 0 ∧ a = divisor := sorry

theorem find_initial_numbers_positive_case (divisor iterations : Int)
  (h1 : divisor > 0) (h2 : iterations > 0) :
  let (a, b) := find_initial_numbers divisor iterations
  a ≥ divisor ∧ b ≥ divisor := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded