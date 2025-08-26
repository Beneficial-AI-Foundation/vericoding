function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).

// <vc-helpers>
// </vc-helpers>

method powerIter(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
// <vc-code>
{
  p := 1.0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant p == power(b, i)
  {
    p := p * b;
    i := i + 1;
  }
}
// </vc-code>

lemma distributiveProperty(x: real, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, a+b)
{
    if a == 0 {
        assert
            power(x, a) * power(x, b) ==
            power(x, b) ==
            power(x, a + b);
    }
    else {
        distributiveProperty(x, a-1, b);
        assert
            power(x, a) * power(x, b) ==
            (x * power(x, a-1)) * power(x, b) ==
            x * (power(x, a-1) * power(x, b)) ==
            x * power(x, a - 1 + b) ==
            power(x, a + b);
    }
}
// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.