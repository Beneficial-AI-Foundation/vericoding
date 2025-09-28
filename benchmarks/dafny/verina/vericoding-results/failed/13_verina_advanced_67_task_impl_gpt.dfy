// <vc-preamble>
function DecodeRle(lst: seq<(char, nat)>): seq<char>
{
    []
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added a simple identity function for sequences to keep helpers non-empty */
function SeqId<A>(xs: seq<A>): seq<A>
{
  xs
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
  /* code modified by LLM (iteration 2): Implemented terminating run-length encoding loop; removed non-terminating while(true) */
  if |s| == 0 {
    result := [];
  } else {
    var cur := s[0];
    var count: nat := 1;
    var i: nat := 1;
    var acc: seq<(char, nat)> := [];
    while i < |s|
      invariant 1 <= i <= |s|
      invariant count > 0
      invariant |acc| >= 0
      decreases |s| - i
    {
      if s[i] == cur {
        count := count + 1;
      } else {
        acc := acc + [(cur, count)];
        cur := s[i];
        count := 1;
      }
      i := i + 1;
    }
    acc := acc + [(cur, count)];
    result := acc;
  }
}
// </vc-code>
