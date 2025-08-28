/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
  decreases n
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).

// <vc-helpers>
lemma powerAdd(x: real, a: nat, b: nat)
  ensures power(x, a) * power(x, b) == power(x, a + b)
{
  if a == 0 {
    assert power(x, 0) == 1.0;
    assert power(x, 0) * power(x, b) == 1.0 * power(x, b) == power(x, b);
    assert power(x, 0 + b) == power(x, b);
  } else {
    calc {
      power(x, a) * power(x, b);
      == { assert power(x, a) == x * power(x, a-1); }
      (x * power(x, a-1)) * power(x, b);
      == { assert (x * power(x, a-1)) * power(x, b) == x * (power(x, a-1) * power(x, b)); }
      x * (power(x, a-1) * power(x, b));
      == { powerAdd(x, a-1, b); }
      x * power(x, (a-1) + b);
      == { assert (a-1) + b == a + b - 1; }
      x * power(x, a + b - 1);
      == { assert power(x, a + b) == x * power(x, a + b - 1); }
      power(x, a + b);
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method PowerIter(x: real, n: nat) returns (p: real)
  ensures p == power(x, n)
{
  p := 1.0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant p == power(x, i)
  {
    p := p * x;
    i := i + 1;
  }
  assert i == n;
  assert p == power(x, n);
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.

// A simple test case to make sure the specification is adequate.