// <vc-preamble>
function DecodeRle(lst: seq<(char, nat)>): seq<char>
{
    []
}
// </vc-preamble>

// <vc-helpers>
function DecodeRle(lst: seq<(char, nat)>): seq<char>
  decreases |lst|
{
  if |lst| == 0 then []
  else seq(lst[0].1, _ => lst[0].0) + DecodeRle(lst[1..])
}
// </vc-helpers>

// <vc-spec>
method RunLengthEncode(s: seq<char>) returns (result: seq<(char, nat)>)
    ensures
        forall i :: 0 <= i < |result| ==> result[i].1 > 0
    ensures
        forall i :: 0 <= i < |result| ==> i + 1 < |result| ==> result[i].0 != result[i + 1].0
    ensures
        DecodeRle(result) == s
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Implemented the run-length encoding with loops to group consecutive characters. */
  result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < |result| ==> result[k].1 > 0
    invariant forall k :: 0 <= k < |result| ==> k + 1 < |result| ==> result[k].0 != result[k + 1].0
    invariant DecodeRle(result) == s[..i]
  {
    var ch := s[i];
    var count := 1;
    i := i + 1;
    while i < |s| && s[i] == ch
      invariant count > 0
      invariant i == old(i) + count
      invariant forall j :: old(i) <= j < i ==> s[j] == ch
    {
      count := count + 1;
      i := i + 1;
    }
    result := result + [(ch, count)];
  }
}
// </vc-code>
