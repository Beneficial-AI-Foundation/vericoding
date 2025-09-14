

// <vc-helpers>
// No updates needed
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
// </vc-spec>
// <vc-code>
{
  ghost var origIndices: seq<int> := [];

  var count := 0;
  for i: int := 0 to arr.Length - 1
    invariant 0 <= i <= arr.Length
    invariant count == |{ j: int | 0 <= j < i && arr[j] % 2 == 0 }|
  {
    if arr[i] % 2 == 0 { count := count + 1; }
  }
  evenNumbers := new int[count];
  var idx := 0;
  for i: int := 0 to arr.Length - 1
    invariant 0 <= i <= arr.Length
    invariant idx >= 0 && idx <= count
    invariant |origIndices| == idx
    invariant forall j :: 0 <= j < |origIndices| ==> 0 <= origIndices[j] < i
    invariant forall j, k :: 0 <= j < k < |origIndices| ==> origIndices[j] < origIndices[k]
    invariant forall j :: 0 <= j < |origIndices| ==> evenNumbers[j] == arr[origIndices[j]]
  {
    if arr[i] % 2 == 0 {
      evenNumbers[idx] := arr[i];
      idx := idx + 1;
      origIndices := origIndices + [i];
    }
  }
}
// </vc-code>

