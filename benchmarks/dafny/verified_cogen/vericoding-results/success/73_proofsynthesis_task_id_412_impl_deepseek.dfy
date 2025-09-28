// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsEven(i: int): bool { i % 2 == 0 }
// </vc-helpers>

// <vc-spec>
method RemoveOdds(arr: array<int>) returns (even_list: seq<int>)
    ensures |even_list| <= arr.Length
    ensures forall i :: 0 <= i < |even_list| ==> even_list[i] % 2 == 0
// </vc-spec>
// <vc-code>
{
  even_list := [];
  var index := 0;
  while index < arr.Length
    invariant |even_list| <= index
    invariant index <= arr.Length
    invariant forall j :: 0 <= j < |even_list| ==> even_list[j] % 2 == 0
  {
    if IsEven(arr[index]) {
      even_list := even_list + [arr[index]];
    }
    index := index + 1;
  }
}
// </vc-code>
