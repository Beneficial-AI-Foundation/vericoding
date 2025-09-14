// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 2): [changed loop invariants to use iset] */
  result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    invariant iset(result) == iset(s[..i])
  {
    var current_element := s[i];
    var is_present := false;
    var j := 0;
    while j < |result|
      invariant 0 <= j <= |result|
      invariant is_present <==> current_element in result[..j]
    {
      if result[j] == current_element {
        is_present := true;
      }
      j := j + 1;
    }

    if !is_present {
      result := result + [current_element];
    }
    i := i + 1;
  }
}
// </vc-code>
