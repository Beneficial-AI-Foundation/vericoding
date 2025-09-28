// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FilterOddNumbers(arr: array<int>) returns (odd_list: seq<int>)
    ensures |odd_list| == |set i | 0 <= i < arr.Length && arr[i] % 2 != 0|
    ensures forall x :: x in odd_list ==> x % 2 != 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 != 0 ==> arr[i] in odd_list
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added ghost variable to track indices of odd numbers for cardinality proof */
  odd_list := [];
  ghost var odd_indices := {};
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall x :: x in odd_list ==> x % 2 != 0
    invariant forall j :: 0 <= j < i && arr[j] % 2 != 0 ==> arr[j] in odd_list
    invariant odd_indices == set j | 0 <= j < i && arr[j] % 2 != 0
    invariant |odd_list| == |odd_indices|
  {
    if arr[i] % 2 != 0 {
      odd_list := odd_list + [arr[i]];
      odd_indices := odd_indices + {i};
    }
    i := i + 1;
  }
  assert odd_indices == set j | 0 <= j < arr.Length && arr[j] % 2 != 0;
}
// </vc-code>
