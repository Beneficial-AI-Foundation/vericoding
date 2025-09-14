// <vc-preamble>
predicate IsSpaceCommaDotSpec(c: char)
{
    (c == ' ') || (c == ',') || (c == '.')
}

function InnerExprReplaceWithColon(str1: seq<char>, k: int): char
    requires 0 <= k < |str1|
{
    if IsSpaceCommaDotSpec(str1[k]) then
        ':'
    else
        str1[k]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple mapping function for space/comma/dot to ':' */
function ReplaceCharIfSpaceCommaDot(c: char): char {
  if IsSpaceCommaDotSpec(c) then ':' else c
}
// </vc-helpers>

// <vc-spec>
method ReplaceWithColon(str1: seq<char>) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall k :: 0 <= k < |result| ==> result[k] == InnerExprReplaceWithColon(str1, k)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): removed invalid cast; build result iteratively with proper invariants */
  var i := 0;
  result := [];
  while i < |str1|
    invariant 0 <= i <= |str1|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == InnerExprReplaceWithColon(str1, k)
    decreases |str1| - i
  {
    result := result + [InnerExprReplaceWithColon(str1, i)];
    i := i + 1;
  }
}
// </vc-code>
