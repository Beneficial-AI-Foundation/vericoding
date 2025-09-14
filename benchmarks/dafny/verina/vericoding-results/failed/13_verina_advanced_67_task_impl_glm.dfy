// <vc-preamble>
function DecodeRle(lst: seq<(char, nat)>): seq<char>
{
    []
}
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 2): fixed missing braces for else block */
  if |s| == 0 then
    result := [];
  else
  {
    var currentChar := s[0];
    var count := 1;
    result := [];
    var i := 1;
    while i < |s|
    {
      if s[i] == currentChar then
        count := count + 1;
      else
      {
        result := result + [(currentChar, count)];
        currentChar := s[i];
        count := 1;
      }
      i := i + 1;
    }
    result := result + [(currentChar, count)];
  }
}
// </vc-code>
