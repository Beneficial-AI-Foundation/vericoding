// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to allow array slicing */
function ToSeq(a: array<int>): seq<int> reads a { a[..] }
// </vc-helpers>

// <vc-spec>
method RemoveKthElement(list: array<int>, k: int) returns (new_list: seq<int>)
    requires list.Length > 0
    requires 0 < k < list.Length
    ensures new_list == list[0..k-1] + list[k..list.Length]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): convert array to seq and concatenate slices to remove kth element */
  var s := ToSeq(list);
  new_list := s[0..k-1] + s[k..list.Length];
}
// </vc-code>
