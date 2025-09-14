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
/* helper modified by LLM (iteration 2): proves InnerExprReplaceWithColon yields ':' or original char */
lemma InnerExprReplaceWithColon_CharacterOrSame(str: seq<char>, k: int)
  requires 0 <= k < |str|
  ensures InnerExprReplaceWithColon(str, k) == ':' || InnerExprReplaceWithColon(str, k) == str[k]
{
  if IsSpaceCommaDotSpec(str[k]) {
    assert InnerExprReplaceWithColon(str, k) == ':';
  } else {
    assert InnerExprReplaceWithColon(str, k) == str[k];
  }
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
  /* code modified by LLM (iteration 2): build result by replacing spaces/commas/dots with ':' */
  var r: seq<char> := [];
  var k := 0;
  while k < |str1|
    invariant 0 <= k <= |str1|
    invariant |r| == k
    invariant forall i :: 0 <= i < k ==> r[i] == InnerExprReplaceWithColon(str1, i)
  {
    r := r + [InnerExprReplaceWithColon(str1, k)];
    k := k + 1;
  }
  result := r;
}

// </vc-code>
