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

// </vc-helpers>

// <vc-spec>
method ReplaceWithColon(str1: seq<char>) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall k :: 0 <= k < |result| ==> result[k] == InnerExprReplaceWithColon(str1, k)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added loop invariant to ensure postconditions are satisfied */
  var temp: seq<char> := [];
  for i: nat := 0 to |str1|
    invariant |temp| == i
    invariant forall j: nat :: j < i ==> temp[j] == InnerExprReplaceWithColon(str1, j)
  {
    temp := temp + [InnerExprReplaceWithColon(str1, i)];
  }
  result := temp;
}
// </vc-code>
