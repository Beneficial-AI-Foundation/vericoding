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
lemma PowerZero(x: real)
  ensures power(x, 0) == 1.0
{
}

lemma PowerInductive(x: real, n: nat)
  requires n > 0
  ensures power(x, n) == x * power(x, n-1)
{
}

lemma PowerHelper(x: real, k: nat, m: nat)
  ensures power(x, k + m) == power(x, k) * power(x, m)
  decreases k
{
  if k > 0 {
    PowerHelper(x, k-1, m);
  }
}
// </vc-helpers>

// <vc-spec>
method powerIter(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
// </vc-spec>
// <vc-code>
{
  p := 1.0;
  var counter := n;
  
  while counter > 0
    invariant p * power(b, counter) == power(b, n)
    decreases counter
  {
    p := p * b;
    counter := counter - 1;
  }
  
  if n == 0 {
    PowerZero(b);
  } else {
    PowerInductive(b, n);
  }
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.