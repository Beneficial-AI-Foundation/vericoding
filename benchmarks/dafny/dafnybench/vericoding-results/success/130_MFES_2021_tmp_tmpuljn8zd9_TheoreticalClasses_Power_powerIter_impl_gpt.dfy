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
lemma power_step(x: real, i: nat)
  ensures power(x, i+1) == x * power(x, i)
{
  assert i + 1 != 0;
}
// </vc-helpers>

// <vc-spec>
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  var acc: real := 1.0;
  while i < n
    invariant i <= n
    invariant acc == power(x, i)
    decreases n - i
  {
    var j: nat := i;
    var a: real := acc;
    acc := x * a;
    i := j + 1;
    assert a == power(x, j);
    power_step(x, j);
    assert acc == x * power(x, j);
    assert acc == power(x, j + 1);
    assert i == j + 1;
    assert acc == power(x, i);
  }
  p := acc;
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.

// A simple test case to make sure the specification is adequate.