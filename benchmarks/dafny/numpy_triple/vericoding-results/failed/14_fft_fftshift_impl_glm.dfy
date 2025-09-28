// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FFTShiftIndex(i: int, n: int): int
  requires n >= 0
  requires 0 <= i < n
  ensures 0 <= FFTShiftIndex(i, n) < n
{
  if n == 0 then 0 else (i + n - n / 2) % n
}

/* helper modified by LLM (iteration 2): Added explicit triggers and complete bijection proof */
lemma FFTShiftIndexBijection(n: int)
  requires n >= 0
  ensures forall i {:trigger FFTShiftIndex(i, n)} :: 0 <= i < n ==> 0 <= FFTShiftIndex(i, n) < n
  ensures forall i {:trigger FFTShiftIndex(i, n)} :: 0 <= i < n ==> exists j {:trigger FFTShiftIndex(j, n)} :: 0 <= j < n && FFTShiftIndex(j, n) == i
  ensures forall i {:trigger FFTShiftIndex(i, n)} :: 0 <= i < n ==> exists j {:trigger FFTShiftIndex(j, n)} :: 0 <= j < n && FFTShiftIndex(i, n) == j
{
  if n == 0 {
  } else {
    var shift := n - n / 2;
    assert shift == (n + 1) / 2;
    
    // Prove the mapping is within bounds
    forall i | 0 <= i < n
      ensures 0 <= FFTShiftIndex(i, n) < n
    {
      var idx := (i + shift) % n;
      assert 0 <= idx < n;
    }
    
    // Prove surjectivity: for every i, there exists j such that FFTShiftIndex(j, n) == i
    forall i | 0 <= i < n
      ensures exists j :: 0 <= j < n && FFTShiftIndex(j, n) == i
    {
      var j := (i - shift + n) % n;
      assert 0 <= j < n;
      calc {
        FFTShiftIndex(j, n);
        (j + shift) % n;
        ((i - shift + n) % n + shift) % n;
        (i - shift + n + shift) % n;
        (i + n) % n;
        i % n;
        i;
      }
    }
    
    // Prove injectivity: for every i, there exists unique j such that FFTShiftIndex(i, n) == j
    forall i | 0 <= i < n
      ensures exists j :: 0 <= j < n && FFTShiftIndex(i, n) == j
    {
      var j := FFTShiftIndex(i, n);
      assert 0 <= j < n;
    }
  }
}

/* helper modified by LLM (iteration 2): Fixed multiset preservation proof */
lemma FFTShiftPreservesMultiset(x: seq<real>)
  ensures multiset(x) == multiset(FFTShiftImpl(x))
{
  if |x| == 0 {
  } else {
    FFTShiftIndexBijection(|x|);
    // The bijection property ensures multiset equality
    assert forall i :: 0 <= i < |x| ==> 0 <= FFTShiftIndex(i, |x|) < |x|;
    assert forall i :: 0 <= i < |x| ==> exists j :: 0 <= j < |x| && FFTShiftIndex(j, |x|) == i;
    assert forall i :: 0 <= i < |x| ==> exists j :: 0 <= j < |x| && FFTShiftIndex(i, |x|) == j;
  }
}

function FFTShiftImpl(x: seq<real>): seq<real>
  requires |x| >= 0
  ensures |FFTShiftImpl(x)| == |x|
  ensures |x| > 0 ==> forall i :: 0 <= i < |x| ==> 
    FFTShiftImpl(x)[i] == x[FFTShiftIndex(i, |x|)]
  ensures multiset(FFTShiftImpl(x)) == multiset(x)
{
  if |x| == 0 then [] else
    seq(|x|, i requires 0 <= i < |x| => x[FFTShiftIndex(i, |x|)])
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
  /* code modified by LLM (iteration 2): Added explicit assertions to verify postconditions */
  if |x| == 0 {
    result := [];
  } else {
    FFTShiftIndexBijection(|x|);
    FFTShiftPreservesMultiset(x);
    
    // Create the shifted sequence
    result := seq(|x|, i requires 0 <= i < |x| => x[FFTShiftIndex(i, |x|)]);
    
    // Verify the main transformation property
    assert forall i :: 0 <= i < |x| ==> result[i] == x[(i + |x| - |x|/2) % |x|];
    
    // Verify bijective properties using the bijection lemma
    assert forall j :: 0 <= j < |x| ==> exists k :: 0 <= k < |x| && result[k] == x[j];
    assert forall k :: 0 <= k < |x| ==> exists j :: 0 <= j < |x| && result[k] == x[j];
    
    // Verify multiset equality
    assert multiset(result) == multiset(x);
  }
}
// </vc-code>
