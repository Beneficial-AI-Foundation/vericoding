// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplified helpers with explicit triggers and direct arithmetic */
lemma ModuloProperties(n: int)
  requires n > 0
  ensures forall i :: 0 <= i < n ==> 0 <= (i + n - n/2) % n < n
  ensures forall i :: 0 <= i < n ==> 0 <= (i - (n - n/2) + n) % n < n
{
  forall i | 0 <= i < n
  {
    assert (i + n - n/2) % n >= 0 && (i + n - n/2) % n < n;
    assert (i - (n - n/2) + n) % n >= 0 && (i - (n - n/2) + n) % n < n;
  }
}

lemma BijectiveMapping(x: seq<real>, result: seq<real>)
  requires |x| > 0
  requires |result| == |x|
  requires forall i :: 0 <= i < |x| ==> result[i] == x[(i + |x| - |x|/2) % |x|]
  ensures forall j :: 0 <= j < |x| ==> exists k :: 0 <= k < |x| && result[k] == x[j]
  ensures forall k :: 0 <= k < |x| ==> exists j :: 0 <= j < |x| && result[k] == x[j]
{
  var n := |x|;
  var shift := n - n/2;
  
  forall j | 0 <= j < n
    ensures exists k :: 0 <= k < n && result[k] == x[j]
  {
    var k := (j - shift + n) % n;
    assert 0 <= k < n;
    calc {
      result[k];
      x[(k + shift) % n];
      x[((j - shift + n) % n + shift) % n];
      x[j];
    }
  }
  
  forall k | 0 <= k < n
    ensures exists j :: 0 <= j < n && result[k] == x[j]
  {
    var j := (k + shift) % n;
    assert 0 <= j < n;
    assert result[k] == x[j];
  }
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
  /* code modified by LLM (iteration 5): Streamlined implementation with direct lemma calls */
  if |x| == 0 {
    return [];
  }
  
  var n := |x|;
  var shift := n - n/2;
  
  ModuloProperties(n);
  
  result := seq(n, i => x[(i + shift) % n]);
  
  BijectiveMapping(x, result);
}
// </vc-code>
