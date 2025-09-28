// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsEven(x: int) { x % 2 == 0 }
// </vc-helpers>

// <vc-spec>
method RemoveOdds(arr: array<int>) returns (even_list: seq<int>)
    ensures |even_list| <= arr.Length
    ensures forall i :: 0 <= i < |even_list| ==> even_list[i] % 2 == 0
// </vc-spec>
// <vc-code>
{
  var s: seq<int> := [];
  var i: int := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant |s| <= i
    invariant forall j :: 0 <= j < |s| ==> IsEven(s[j])
    decreases arr.Length - i
  {
    if IsEven(arr[i]) {
      s := s + [arr[i]];
    }
    i := i + 1;
  }
  even_list := s;
}
// </vc-code>
