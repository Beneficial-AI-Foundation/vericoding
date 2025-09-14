// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [fix compilation error by removing invalid cast] */
  var i := 0;
  var res_seq: seq<char> := [];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |res_seq| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> res_seq[k] == ch) && (s[k] != ' ' ==> res_seq[k] == s[k])
  {
    if s[i] == ' ' {
      res_seq := res_seq + [ch];
    } else {
      res_seq := res_seq + [s[i]];
    }
    i := i + 1;
  }
  v := res_seq;
}
// </vc-code>
