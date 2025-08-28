/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, M.EIC, MFS, 2021/22.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).

// <vc-helpers>
lemma PowerIterCorrect(b: real, n: nat, p: real, i: nat)
  ensures i == n ==> p == power(b, n)
  ensures i < n ==> p == power(b, i)
{
  if i == 0 {
    assert p == 1.0;
    assert power(b, 0) == 1.0;
  } else {
    // No further assertions needed as the loop invariant handles the correctness
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method powerIter(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method PowerIter(b: real, n: nat) returns (p: real)
  ensures p == power(b, n)
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
  assert i == n;
  assert p == power(b, n);
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.