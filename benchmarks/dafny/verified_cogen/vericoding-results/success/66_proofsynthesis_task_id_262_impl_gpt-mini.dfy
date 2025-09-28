// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): convert array to sequence */
function SeqOfArray(a: array<int>): seq<int> reads a { a[..] }
// </vc-helpers>

// <vc-spec>
method SplitArray(list: array<int>, l: int) returns (new_list: (seq<int>, seq<int>))
    requires
        list.Length > 0 &&
        0 < l < list.Length
    ensures
        new_list.0 == list[0..l] &&
        new_list.1 == list[l..list.Length]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): split array into two sequences using helper */
  var s := SeqOfArray(list);
  new_list := (s[0..l], s[l..list.Length]);
}
// </vc-code>
