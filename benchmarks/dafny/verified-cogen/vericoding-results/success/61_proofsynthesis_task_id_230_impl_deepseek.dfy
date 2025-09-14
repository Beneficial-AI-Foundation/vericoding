// <vc-preamble>
function InnerExprReplaceBlanksWithChars(str1: seq<char>, ch: char, i: int): char
    requires 0 <= i < |str1|
{
    if str1[i] == ' ' then
        ch
    else
        str1[i]
}
// </vc-preamble>

// <vc-helpers>
function InnerExprResult(str1: seq<char>, ch: char, i: int): char
  requires 0 <= i < |str1|
{
  if str1[i] == ' ' then ch else str1[i]
}

lemma SeqLengthInvariant(str1: seq<char>, result: seq<char>, idx: int)
  requires 0 <= idx <= |str1|
  requires |result| == idx
  ensures |result| <= |str1|
{
}

lemma ElementEqualityInvariant(str1: seq<char>, ch: char, result: seq<char>, idx: int)
  requires 0 <= idx <= |str1|
  requires |result| == idx
  requires forall j :: 0 <= j < idx ==> result[j] == InnerExprResult(str1, ch, j)
{
}
// </vc-helpers>

// <vc-spec>
method ReplaceBlanksWithChars(str1: seq<char>, ch: char) returns (result: seq<char>)
    ensures
        |str1| == |result| &&
        forall i :: 0 <= i < |str1| ==> result[i] == InnerExprReplaceBlanksWithChars(str1, ch, i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed syntax errors and implemented proper sequence construction */
  result := [];
  var idx := 0;
  while idx < |str1|
    invariant 0 <= idx <= |str1|
    invariant |result| == idx
    invariant forall j :: 0 <= j < idx ==> result[j] == InnerExprResult(str1, ch, j)
  {
    SeqLengthInvariant(str1, result, idx);
    ElementEqualityInvariant(str1, ch, result, idx);
    result := result + [InnerExprResult(str1, ch, idx)];
    idx := idx + 1;
  }
  assert |result| == |str1|;
}
// </vc-code>
