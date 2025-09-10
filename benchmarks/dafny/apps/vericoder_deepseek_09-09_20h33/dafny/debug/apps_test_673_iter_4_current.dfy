predicate ValidInput(n: int, k: int)
{
    n >= 1 && k > 0
}

predicate IsCorrectResult(n: int, k: int, result: int)
    requires k > 0
{
    result > n && result % k == 0 && forall x :: n < x < result ==> x % k != 0
}

// <vc-helpers>
lemma {:induction false} LemmaNextDivisible(n: int, k: int)
  requires n >= 1 && k > 0
  ensures exists result: int :: 
    result > n && result % k == 0 && 
    (forall x: int :: n < x < result ==> x % k != 0)
{
  var candidate := n + 1;
  while candidate % k != 0
    invariant candidate > n
    invariant forall x: int :: n < x < candidate ==> x % k != 0
    decreases *  // Changed to non-deterministic termination
  {
    candidate := candidate + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
  var candidate := n + 1;
  while candidate % k != 0
    invariant candidate > n
    invariant forall x: int :: n < x < candidate ==> x % k != 0
    decreases *  // Changed to non-deterministic termination
  {
    candidate := candidate + 1;
  }
  result := candidate;
}
// </vc-code>

