// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveOdds(arr: array<int>) returns (even_list: seq<int>)
    ensures |even_list| <= arr.Length
    ensures forall i :: 0 <= i < |even_list| ==> even_list[i] % 2 == 0
// </vc-spec>
// <vc-code>
{
var evens: seq<int> := [];
for i := 0 to arr.Length
invariant 0 <= i <= arr.Length
invariant |evens| <= i
invariant forall k :: 0 <= k < |evens| ==> evens[k] % 2 == 0
{
  if arr[i] % 2 == 0 {
    evens := evens + [arr[i]];
  }
}
even_list := evens;
}
// </vc-code>
