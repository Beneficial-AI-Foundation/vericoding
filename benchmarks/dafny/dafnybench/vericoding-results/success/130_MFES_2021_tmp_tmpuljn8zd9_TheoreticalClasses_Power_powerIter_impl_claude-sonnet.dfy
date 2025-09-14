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
lemma powerIterInvariant(x: real, i: nat, n: nat, p: real)
  requires i <= n
  requires p == power(x, i)
  ensures p * power(x, n - i) == power(x, n)
  decreases n - i
{
  if i == n {
    assert power(x, n - i) == power(x, 0) == 1.0;
  } else {
    assert power(x, n - i) == x * power(x, n - i - 1);
    powerIterInvariant(x, i + 1, n, p * x);
  }
}
// </vc-helpers>

// <vc-spec>
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// <vc-code>
{
  p := 1.0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant p == power(x, i)
    decreases n - i
  {
    p := p * x;
    i := i + 1;
  }
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.

// A simple test case to make sure the specification is adequate.