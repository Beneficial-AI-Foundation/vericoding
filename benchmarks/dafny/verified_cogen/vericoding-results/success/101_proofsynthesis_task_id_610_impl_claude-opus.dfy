// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveKthElement(list: array<int>, k: int) returns (new_list: seq<int>)
    requires list.Length > 0
    requires 0 < k < list.Length
    ensures new_list == list[0..k-1] + list[k..list.Length]
// </vc-spec>
// <vc-code>
{
  new_list := list[0..k-1] + list[k..list.Length];
}
// </vc-code>
