// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): keeping correct helper, fixing usage in vc-code */
function GetHead(s: seq<int>): int
  requires |s| > 0
{ s[0] }
// </vc-helpers>

// <vc-spec>
method GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
    ensures |result| == |lst|
    ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): replaced sequence comprehension with a while loop for explicit proof */
  result := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == lst[j][0]
    decreases |lst| - i
  {
    // Dafny can prove |lst[i]| > 0 from the method's requires clause and the loop invariant i < |lst|.
    // This satisfies the precondition for GetHead.
    result := result + [GetHead(lst[i])];
    i := i + 1;
  }
}
// </vc-code>
