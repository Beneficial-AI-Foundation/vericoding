// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int {
  if a < b then a else b
}

/* helper modified by LLM (iteration 5): Added min function to resolve compilation error */
function Contains(arr: array<real>, value: real, start: int, end: int): bool
  requires 0 <= start <= end <= arr.Length
  reads arr
  decreases end - start
{
  if start >= end then false
  else if arr[start] == value then true
  else Contains(arr, value, start + 1, end)
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
  /* code modified by LLM (iteration 5): Fixed min function references and loop bounds */
  if a.Length == 0 || b.Length == 0 {
    result := new real[0];
    return;
  }
  
  var size := min(a.Length, b.Length);
  var temp := new real[size];
  var index := 0;

  for i := 0 to a.Length - 1
    invariant 0 <= index <= min(i, size)
    invariant index <= size
    invariant forall k :: 0 <= k < index ==> Contains(temp, temp[k], 0, index)
    invariant forall k, l :: 0 <= k < i && 0 <= l < b.Length ==> (
      (a[k] == b[l] ==> exists m :: 0 <= m < index && temp[m] == a[k]) &&
      (a[k] != b[l] ==> !exists m :: 0 <= m < index && temp[m] == a[k])
    )
  {
    var found := Contains(b, a[i], 0, b.Length);
    
    if found && !Contains(temp, a[i], 0, index) {
      if index < size {
        temp[index] := a[i];
        index := index + 1;
      }
    }
  }
  
  var resultArr := new real[index];
  if index > 0 {
    for i := 0 to index - 1
      invariant forall j :: 0 <= j < i ==> resultArr[j] == temp[j]
    {
      resultArr[i] := temp[i];
    }
  }
  
  result := resultArr;
}
// </vc-code>
