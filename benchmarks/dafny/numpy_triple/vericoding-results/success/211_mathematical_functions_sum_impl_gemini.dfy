// <vc-preamble>
// Helper function to compute sum of array elements recursively
function Sum(s: seq<real>): real
{
    if |s| == 0 then 0.0
    else s[0] + Sum(s[1..])
}

// Predicate to check if all elements in sequence are zero
predicate AllZero(s: seq<real>)
{
    forall i :: 0 <= i < |s| ==> s[i] == 0.0
}

/**
 * Sum of array elements - computes the sum of all elements in the vector.
 * For empty vectors, returns 0 as the identity element of addition.
 * This is a reduction operation that applies addition across all elements.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause for clarity */
lemma SumOfAllZeros(s: seq<real>)
  requires AllZero(s)
  ensures Sum(s) == 0.0
  decreases |s|
{
  if |s| > 0 {
    SumOfAllZeros(s[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method sum(a: array<real>) returns (result: real)
    requires true
    ensures result == Sum(a[..])  // Result equals sum of all elements using recursive definition
    ensures a.Length == 0 ==> result == 0.0  // Empty array returns 0 (additive identity)
    ensures AllZero(a[..]) ==> result == 0.0  // If all elements are zero, result is zero
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added loop invariant for AllZero case */
  result := 0.0;
  var i := a.Length;
  while i > 0
    invariant 0 <= i <= a.Length
    invariant result == Sum(a[i..])
    invariant AllZero(a[i..]) ==> result == 0.0
  {
    i := i - 1;
    result := a[i] + result;
  }
}
// </vc-code>
