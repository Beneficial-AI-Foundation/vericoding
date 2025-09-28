// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed postcondition with explicit equivalence */
function setToSeqHelper(s: seq<int>, idx: int): (r: seq<int>)
  requires 0 <= idx <= |s|
  ensures forall i: int, j: int :: 0 <= i < j < |r| ==> r[i] != r[j]
  ensures forall i: int :: 0 <= i < |r| ==> exists j: int :: 0 <= j < |s| && s[j] == r[i]
  ensures forall i: int :: 0 <= i < |s| ==> (exists j: int :: 0 <= j < |r| && r[j] == s[i]) <==> (exists k: int :: 0 <= k < idx && s[k] == s[i])
{
  if idx == 0 then
    []
  else
    var prefix := setToSeqHelper(s, idx - 1);
    var lastElem := s[idx - 1];
    if exists k: int :: 0 <= k < |prefix| && prefix[k] == lastElem then
      prefix
    else
      prefix + [lastElem]
}
// </vc-helpers>

// <vc-spec>
method SetToSeq(s: seq<int>) returns (result: seq<int>)
    ensures
        // All elements are unique in the result  
        forall i: int, j: int :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures
        // Every element in result is in s
        forall i: int :: 0 <= i < |result| ==> 
            exists j: int :: 0 <= j < |s| && s[j] == result[i]
    ensures
        // Every element in s is in result
        forall i: int :: 0 <= i < |s| ==> 
            exists j: int :: 0 <= j < |result| && result[j] == s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): direct call to fixed helper function */
  result := setToSeqHelper(s, |s|);
}
// </vc-code>
