// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ReverseSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else ReverseSeq(s[1..]) + [s[0]]
}
// </vc-helpers>

// <vc-spec>
method ReverseToK(list: array<int>, n: int) returns (reversed_list: seq<int>)
    requires
        list.Length > 0 &&
        0 < n < list.Length
    ensures
        reversed_list == list[0..n][..n] + list[n..list.Length]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): removed incorrect reversal to match postcondition */
  var prefix := list[0..n];
  var suffix := list[n..list.Length];
  // The postcondition requires `list[0..n][..n]`, which is equivalent to `list[0..n]` (the prefix).
  // The previous implementation incorrectly reversed the prefix.
  reversed_list := prefix + suffix;
}
// </vc-code>
