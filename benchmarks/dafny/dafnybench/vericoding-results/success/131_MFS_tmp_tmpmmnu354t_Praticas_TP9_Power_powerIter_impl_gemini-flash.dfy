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
lemma lemma_power_iter(b: real, n: nat)
  ensures forall k :: 0 <= k <= n ==> (k == 0 ==> 1.0 == power(b,0) && power(b,k) == 1.0) && (k > 0 ==> b * power(b, k-1) == power(b,k))
  decreases n
{
  if n > 0 {
    lemma_power_iter(b, n-1);
    // Add additional assertions to help the verifier
    assert b * power(b, n-1) == power(b,n); // This specific step is often useful
  } else {
    assert 1.0 == power(b,0); // Base case
  }
}
// </vc-helpers>

// <vc-spec>
method powerIter(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
// </vc-spec>
// <vc-code>
{
    var current_p := 1.0;
    var i := 0;
    lemma_power_iter(b, n); // Call the lemma once before the loop
    while i < n
        invariant 0 <= i <= n
        invariant current_p == power(b, i)
        decreases n - i
    {
        current_p := current_p * b;
        i := i + 1;
        // The loop invariant current_p == power(b,i) implies
        // current_p_prev * b == power(b, i_prev) * b
        // And we know from the lemma that power(b, i_prev) * b == power(b, i_prev + 1), which is power(b,i)
    }
    return current_p;
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// A simple test case to make sure the specification is adequate.