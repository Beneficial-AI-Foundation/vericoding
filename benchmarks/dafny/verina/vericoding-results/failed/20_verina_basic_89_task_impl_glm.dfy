// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): defined Contains function for sequence membership */
function Contains(seq: seq<int>, value: int): bool
{
  exists i: int :: 0 <= i < |seq| && seq[i] == value
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
  /* code modified by LLM (iteration 4): fixed compilation error by replacing 'in' with Contains function */
  result := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall j: int, k: int :: 0 <= j < k < |result| ==> result[j] != result[k]
    invariant forall x: int :: Contains(result, x) <==> (exists j: int :: 0 <= j < i && s[j] == x)
  {
    if !Contains(result, s[i]) then
    {
      result := result + [s[i]];
    }
  }
}
// </vc-code>
