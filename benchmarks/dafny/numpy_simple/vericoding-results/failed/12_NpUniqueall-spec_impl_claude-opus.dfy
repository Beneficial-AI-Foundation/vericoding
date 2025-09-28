// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate InArray(arr: array<int>, val: int, len: int)
  reads arr
  requires 0 <= len <= arr.Length
{
  exists j :: 0 <= j < len && arr[j] == val
}

method Contains(arr: array<int>, val: int, len: int) returns (found: bool)
  requires 0 <= len <= arr.Length
  ensures found == InArray(arr, val, len)
{
  var i := 0;
  found := false;
  while i < len
    invariant 0 <= i <= len
    invariant found == (exists j :: 0 <= j < i && arr[j] == val)
  {
    if arr[i] == val {
      found := true;
      break;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method UniqueAll(arr: array<int>) returns (ret: array<int>)
    ensures
        ret.Length <= arr.Length &&
        (forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < ret.Length && ret[j] == arr[i]) &&
        (forall i, j :: 0 <= i < ret.Length && 0 <= j < i ==> ret[i] != ret[j])
// </vc-spec>
// <vc-code>
{
  var result := new int[arr.Length];
  var count := 0;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= count <= i
    invariant count <= result.Length
    invariant forall j :: 0 <= j < i ==> exists k :: 0 <= k < count && result[k] == arr[j]
    invariant forall j, k :: 0 <= j < count && 0 <= k < j ==> result[j] != result[k]
    invariant forall j :: 0 <= j < count ==> exists k :: 0 <= k < i && arr[k] == result[j]
  {
    var found := Contains(result, arr[i], count);
    if !found {
      result[count] := arr[i];
      count := count + 1;
    }
    i := i + 1;
  }
  
  ret := new int[count];
  i := 0;
  while i < count
    invariant 0 <= i <= count
    invariant forall j :: 0 <= j < i ==> ret[j] == result[j]
  {
    ret[i] := result[i];
    i := i + 1;
  }
}
// </vc-code>
