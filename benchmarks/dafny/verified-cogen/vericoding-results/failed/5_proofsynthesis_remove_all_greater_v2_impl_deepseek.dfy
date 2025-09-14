// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix syntax error and simplify lemmas */
function FilterSeq(s: seq<int>, e: int): seq<int> 
{
  if |s| == 0 then []
  else (
    var head := s[0];
    var tail := s[1..];
    if head <= e then [head] + FilterSeq(tail, e)
    else FilterSeq(tail, e)
  )
}

lemma SequenceFilterLemma(s: seq<int>, e: int) 
  ensures forall k :: 0 <= k < |FilterSeq(s, e)| ==> FilterSeq(s, e)[k] <= e 
{
  if |s| == 0 {
  } else {
    var head := s[0];
    var tail := s[1..];
    SequenceFilterLemma(tail, e);
    if head <= e {
    } else {
    }
  }
}

lemma SequencePreservationLemma(s: seq<int>, e: int) 
  ensures forall k :: 0 <= k < |s| && s[k] <= e ==> exists j :: 0 <= j < |FilterSeq(s, e)| && FilterSeq(s, e)[j] == s[k] 
{
  if |s| == 0 {
  } else {
    var head := s[0];
    var tail := s[1..];
    SequencePreservationLemma(tail, e);
    if head <= e {
    } else {
    }
  }
}
// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)
    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && (exists j :: 0 <= j < v.Length && v[j] == result[k])
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> (exists j :: 0 <= j < result.Length && result[j] == v[k])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix syntax error and simplify implementation */
{
    var filtered := FilterSeq(v[..], e);
    result := new int[|filtered|];
    var i := 0;
    
    while i < |filtered|
        invariant 0 <= i <= |filtered|
        invariant forall k :: 0 <= k < i ==> result[k] == filtered[k]
    {
        result[i] := filtered[i];
        i := i + 1;
    }
    
    SequenceFilterLemma(v[..], e);
    SequencePreservationLemma(v[..], e);
}
// </vc-code>
