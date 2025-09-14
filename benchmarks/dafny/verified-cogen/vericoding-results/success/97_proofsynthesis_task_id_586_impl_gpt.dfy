// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method SplitAndAppend(list: array<int>, n: int) returns (new_list: seq<int>)
    requires list.Length > 0
    requires 0 < n < list.Length
    ensures new_list == list[n..list.Length] + list[0..n]
// </vc-spec>
// <vc-code>
{
  new_list := list[n..list.Length] + list[0..n];
}
// </vc-code>
