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
  even_list := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant |even_list| <= i
    invariant forall k :: 0 <= k < |even_list| ==> even_list[k] % 2 == 0
  {
    if arr[i] % 2 == 0 {
      even_list := even_list + [arr[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
