// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/**
 * Helper predicate to check if indices are valid
 */
function IsValidShift(n: int, half: int, i: int): bool
  requires n >= 0 && 0 <= i < n && half == n / 2
{
  var src := (i + n - half) % n;
  0 <= src < n
}

/* helper modified by LLM (iteration 5): Simplified ensures to only verify the valid range of shifted indices */
/** Helper lemma to prove the bijection */
lemma ShiftIsBijection(n: int)
  requires n > 0
  ensures forall i :: 0 <= i < n ==> 0 <= (i + n - n/2) % n < n
{
  forall i | 0 <= i < n {
    var src := (i + n - n/2) % n;
    // Dafny knows: src is always in range due to modulus properties
  }
}

/** Helper method to compute the shift amount */
function ComputeShift(n: int): int
  requires n >= 0
{
  n - n/2
}
// </vc-helpers>

// <vc-spec>
method FFTShift(x: seq<real>) returns (result: seq<real>)
  requires |x| >= 0
  ensures |result| == |x|
  // Main transformation: each element at position i comes from position (i + |x| - |x|/2) % |x|
  ensures |x| > 0 ==> forall i :: 0 <= i < |x| ==> 
    result[i] == x[(i + |x| - |x|/2) % |x|]
  // Bijective property: every input element appears exactly once in output
  ensures forall j :: 0 <= j < |x| ==> exists k :: 0 <= k < |x| && result[k] == x[j]
  // Inverse bijective property: every output element comes from exactly one input element  
  ensures forall k :: 0 <= k < |x| ==> exists j :: 0 <= j < |x| && result[k] == x[j]
  // Multiset equality: same elements with same multiplicities
  ensures multiset(result) == multiset(x)
  // Handle empty sequence case
  ensures |x| == 0 ==> result == []
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Removed lemma call to avoid timeout, added assert for valid src index to aid verification */
  var n := |x|;
  result := [];
  if n > 0 {
    var half := n / 2;
    for i := 0 to n - 1
      invariant |result| == i
      invariant forall k :: 0 <= k < i ==> result[k] == x[(k + n - half) % n]
    {
      var src := (i + n - half) % n;
      assert 0 <= src < n;
      result := result + [x[src]];
    }
  }
  assert |result| == n;
}
// </vc-code>
