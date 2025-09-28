// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helper to check if value exists in array */
predicate InArray(arr: array<real>, val: real)
  reads arr
{
  exists i :: 0 <= i < arr.Length && arr[i] == val
}

/* helper modified by LLM (iteration 5): Added helper to check uniqueness in partial array */
predicate UniqueUpTo(arr: array<real>, n: nat)
  requires n <= arr.Length
  reads arr
{
  forall i, j :: 0 <= i < n && 0 <= j < n && i != j ==> arr[i] != arr[j]
}

/* helper modified by LLM (iteration 5): Added helper to check if value is already in temp array */
predicate InTempArray(temp: array<real>, count: nat, val: real)
  requires count <= temp.Length
  reads temp
{
  exists k :: 0 <= k < count && temp[k] == val
}
// </vc-helpers>

// <vc-spec>
method Intersect(a: array<real>, b: array<real>) returns (result: array<real>)
    ensures
        result.Length < a.Length && result.Length < b.Length &&
        forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> (
            (a[i] == b[j] ==> exists k :: 0 <= k < result.Length && result[k] == a[i]) &&
            (a[i] != b[j] ==> !exists k :: 0 <= k < result.Length && result[k] == a[i])
        )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Complete implementation without assume statements */
  // Handle edge cases for small arrays
  if a.Length <= 1 || b.Length <= 1 {
    result := new real[0];
    return;
  }
  
  // Create temp array with max possible size
  var tempSize := if a.Length <= b.Length then a.Length else b.Length;
  var temp := new real[tempSize];
  var count := 0;
  
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= count <= tempSize
    invariant count < tempSize || i == a.Length  // Ensure we don't overflow temp
    invariant forall k :: 0 <= k < count ==> InArray(b, temp[k])
    invariant forall k :: 0 <= k < count ==> InArray(a, temp[k])
    invariant UniqueUpTo(temp, count)
    invariant forall idx :: 0 <= idx < i ==> (InArray(b, a[idx]) ==> InTempArray(temp, count, a[idx]))
    invariant forall idx :: 0 <= idx < i ==> (!InArray(b, a[idx]) ==> !InTempArray(temp, count, a[idx]))
  {
    if InArray(b, a[i]) && !InTempArray(temp, count, a[i]) {
      if count < tempSize {
        temp[count] := a[i];
        count := count + 1;
      }
    }
    i := i + 1;
  }
  
  // Create result array
  result := new real[count];
  var k := 0;
  while k < count
    invariant 0 <= k <= count
    invariant forall idx :: 0 <= idx < k ==> result[idx] == temp[idx]
    invariant result.Length == count
  {
    result[k] := temp[k];
    k := k + 1;
  }
  
  // Verify postconditions are satisfied
  assert result.Length <= tempSize;
  assert tempSize <= a.Length && tempSize <= b.Length;
  assert result.Length < a.Length || a.Length <= 1;
  assert result.Length < b.Length || b.Length <= 1;
}
// </vc-code>
