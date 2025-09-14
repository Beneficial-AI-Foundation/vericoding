// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): compute max element in prefix, requires valid p */
function MaxPrefix(arr: array<int>, p: int): int
  requires 0 <= p < arr.Length
  reads arr
  decreases p
{
  if p == 0 then arr[0]
  else
    var m := MaxPrefix(arr, p-1);
    if arr[p] > m then arr[p] else m
}

/* helper modified by LLM (iteration 3): compute min element from index to end, requires valid i */
function MinSuffixFrom(arr: array<int>, i: int): int
  requires 0 <= i < arr.Length
  reads arr
  decreases arr.Length - i
{
  if i == arr.Length - 1 then arr[i]
  else
    var m := MinSuffixFrom(arr, i+1);
    if arr[i] < m then arr[i] else m
}
// </vc-helpers>

// <vc-spec>
method Barrier(arr: array<int>, p: int) returns (result: bool)
    requires
        arr.Length > 0 &&
        0 <= p < arr.Length
    ensures
        result == forall k, l :: 0 <= k <= p && p < l < arr.Length ==> arr[k] < arr[l]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): nested loops checking barrier property with maintained invariants */
  if p == arr.Length - 1 {
    result := true;
    return;
  }
  var ok := true;
  var k := 0;
  while k <= p
    invariant 0 <= k <= p+1
    invariant ok ==> (forall i, j :: 0 <= i < k && p < j < arr.Length ==> arr[i] < arr[j])
  {
    var l := p + 1;
    while l < arr.Length
      invariant p+1 <= l <= arr.Length
      invariant ok ==> (forall j :: p < j < l ==> arr[k] < arr[j])
    {
      if !(arr[k] < arr[l]) {
        ok := false;
        break;
      }
      l := l + 1;
    }
    if !ok { break; }
    // After inner loop, l == arr.Length; if ok, arr[k] < arr[j] for all j > p
    if ok {
      assert forall j :: p < j < arr.Length ==> arr[k] < arr[j];
      assert forall i, j :: 0 <= i < k && p < j < arr.Length ==> arr[i] < arr[j];
      assert forall i, j :: 0 <= i < k+1 && p < j < arr.Length ==> arr[i] < arr[j];
    }
    k := k + 1;
  }
  result := ok;
}
// </vc-code>
