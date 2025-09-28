// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): split bijective proof into smaller lemmas for better verification */
function SourceIndex(i: int, n: int): int
  requires n > 0
  requires 0 <= i < n
{
  (i + n - n/2) % n
}

lemma SourceIndexRange(i: int, n: int)
  requires n > 0
  requires 0 <= i < n
  ensures 0 <= SourceIndex(i, n) < n
{
  // Modulo always produces result in [0, n)
}

lemma SourceIndexInjective(i: int, j: int, n: int)
  requires n > 0
  requires 0 <= i < n && 0 <= j < n
  requires SourceIndex(i, n) == SourceIndex(j, n)
  ensures i == j
{
  // If (i + n - n/2) % n == (j + n - n/2) % n
  // Then (i - j) % n == 0
  // Since -n < i - j < n, this means i == j
}

lemma SourceIndexSurjective(k: int, n: int) returns (i: int)
  requires n > 0
  requires 0 <= k < n
  ensures 0 <= i < n
  ensures SourceIndex(i, n) == k
{
  i := (k + n/2) % n;
  // Verify: ((k + n/2) % n + n - n/2) % n
  //       = (k + n/2 + n - n/2) % n
  //       = (k + n) % n
  //       = k
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
/* code modified by LLM (iteration 5): use smaller lemmas and explicit assertions for bijective properties */
{
  if |x| == 0 {
    result := [];
  } else {
    var n := |x|;
    result := seq(n, i requires 0 <= i < n => x[SourceIndex(i, n)]);
    
    // Prove main transformation property
    assert forall i :: 0 <= i < n ==> result[i] == x[SourceIndex(i, n)];
    assert forall i :: 0 <= i < n ==> SourceIndex(i, n) == (i + n - n/2) % n;
    
    // Prove every input element appears in output
    assert forall j :: 0 <= j < n ==> exists k :: 0 <= k < n && result[k] == x[j] by {
      forall j | 0 <= j < n {
        var k := SourceIndexSurjective(j, n);
        assert 0 <= k < n;
        assert SourceIndex(k, n) == j;
        assert result[k] == x[j];
      }
    }
    
    // Prove every output element comes from input
    assert forall k :: 0 <= k < n ==> exists j :: 0 <= j < n && result[k] == x[j] by {
      forall k | 0 <= k < n {
        var j := SourceIndex(k, n);
        SourceIndexRange(k, n);
        assert 0 <= j < n;
        assert result[k] == x[j];
      }
    }
  }
}
// </vc-code>
