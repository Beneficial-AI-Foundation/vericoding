// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed explicit ': bool' return type from predicate declaration to fix compilation error */
predicate IsFirst(i: nat, s: seq<int>)
  requires 0 <= i < |s|
{
  forall j: nat :: 0 <= j < i ==> s[j] != s[i]
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
  /* code modified by LLM (iteration 5): Removed type declaration in sequence comprehension variable to fix syntax error */
  result := seq(i | 0 <= i < |s| && IsFirst(i, s) :: s[i]);
}
// </vc-code>
