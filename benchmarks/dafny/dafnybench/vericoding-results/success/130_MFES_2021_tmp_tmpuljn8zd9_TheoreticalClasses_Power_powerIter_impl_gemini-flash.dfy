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
lemma power_n_plus_m(x: real, a: nat, b: nat)
  ensures power(x, a + b) == power(x, a) * power(x, b)
{
  if a == 0 {
    calc {
      power(x, a + b);
      power(x, b);
      1.0 * power(x, b);
      power(x, 0) * power(x, b);
    }
  } else {
    power_n_plus_m(x, a - 1, b); // Recursively call the lemma
    calc {
      power(x, a + b);
      x * power(x, a - 1 + b);
      { assert power(x, a - 1 + b) == power(x, a - 1) * power(x, b); } // Using the postcondition of the recursive call
      x * (power(x, a - 1) * power(x, b));
      (x * power(x, a - 1)) * power(x, b);
      power(x, a) * power(x, b);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// <vc-code>
{
  var current_p := 1.0;
  var i := 0;
  while i < n
    invariant current_p == power(x, i)
    invariant i <= n
  {
    current_p := current_p * x;
    i := i + 1;
  }
  return current_p;
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.

// A simple test case to make sure the specification is adequate.