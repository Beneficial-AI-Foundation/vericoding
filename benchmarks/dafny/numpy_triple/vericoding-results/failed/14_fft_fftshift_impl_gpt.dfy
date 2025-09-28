// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed function syntax and added shift helper */
function ShiftAmount(n: nat): nat
  ensures 0 <= ShiftAmount(n) <= n
  ensures n == 0 ==> ShiftAmount(n) == 0
{
  if n == 0 then 0 else n - n/2
}

/* helper modified by LLM (iteration 2): lemma to relate slice-concat indexing to modular shift */
lemma SliceShiftIndex(x: seq<real>, k: nat)
  requires k <= |x|
  ensures forall i :: 0 <= i < |x| ==> (x[k..|x|] + x[0..k])[i] == x[(i + k) % |x|]
{
  if |x| == 0 {
  } else {
    var n := |x|;
    forall i | 0 <= i < n
      ensures (x[k..n] + x[0..k])[i] == x[(i + k) % n]
    {
      if i < n - k {
        assert 0 <= i < n - k;
        assert 0 <= k + i < n;
        assert (x[k..n])[i] == x[k + i];
        assert (x[k..n] + x[0..k])[i] == (x[k..n])[i];
        assert (i + k) % n == i + k;
      } else {
        assert n - k <= i < n;
        assert 0 <= i - (n - k) < k;
        assert (x[k..n] + x[0..k])[i] == (x[0..k])[i - (n - k)];
        assert (x[0..k])[i - (n - k)] == x[i - (n - k)];
        assert i + k >= n;
        assert 0 <= i + k - n < n;
        assert (i + k) % n == i + k - n;
      }
    }
  }
}

/* helper modified by LLM (iteration 2): lemma to show multiset is preserved by rotation via slices */
lemma SlicesPartitionMultiset(x: seq<real>, k: nat)
  requires k <= |x|
  ensures multiset(x[k..|x|] + x[0..k]) == multiset(x)
{
  assert x == x[0..k] + x[k..|x|];
  assert multiset(x) == multiset(x[0..k] + x[k..|x|]);
  assert multiset(x[0..k] + x[k..|x|]) == multiset(x[0..k]) + multiset(x[k..|x|]);
  assert multiset(x[k..|x|] + x[0..k]) == multiset(x[k..|x|]) + multiset(x[0..k]);
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
  /* code modified by LLM (iteration 2): implement FFT shift via slice concatenation and use lemmas to prove properties */
  if |x| == 0 {
    result := [];
  } else {
    var n := |x|;
    var k := ShiftAmount(n);
    result := x[k..n] + x[0..k];
    // Bridge k with specification expression
    assert k == n - n/2;
    // Establish element-wise mapping property
    SliceShiftIndex(x, k);
    // Establish multiset preservation
    SlicesPartitionMultiset(x, k);
  }
}
// </vc-code>
