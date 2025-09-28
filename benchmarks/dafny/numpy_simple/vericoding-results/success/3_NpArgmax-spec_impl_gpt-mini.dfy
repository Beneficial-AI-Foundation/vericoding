// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma DummyHelper() ensures true {
}

// </vc-helpers>

// <vc-spec>
method Argmax(arr: array<int>) returns (result: int)
    requires arr.Length > 0
    ensures 
        0 <= result < arr.Length &&
        (forall i :: 0 <= i < result ==> arr[result] > arr[i]) &&
        (forall i :: result < i < arr.Length ==> arr[result] >= arr[i])
// </vc-spec>
// <vc-code>
{
  var n := arr.Length;
  var r := 0;
  var i := 1;
  while i < n
    decreases n - i
    invariant 0 <= r < n
    invariant 0 <= i <= n
    invariant (forall k :: 0 <= k < i ==> arr[r] >= arr[k])
    invariant (forall k :: 0 <= k < r ==> arr[r] > arr[k])
  {
    if arr[i] > arr[r] {
      r := i;
    }
    i := i + 1;
  }
  result := r;
}
// </vc-code>
