// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): completely reworked sort with simpler bubble sort approach */
function Contains(arr: array<int>, x: int): bool
  reads arr
{
  x in arr[..]
}

function IsSorted(arr: array<int>): bool
  reads arr
{
  forall i :: 0 <= i < arr.Length - 1 ==> arr[i] <= arr[i + 1]
}

function HasNoDuplicates(arr: array<int>): bool
  reads arr
{
  forall i, j :: 0 <= i < j < arr.Length ==> arr[i] != arr[j]
}

method Sort(arr: array<int>)
  modifies arr
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  ensures forall i :: 0 <= i < arr.Length - 1 ==> arr[i] <= arr[i + 1]
{
  var n := arr.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    invariant forall k :: 0 <= k < i - 1 ==> arr[k] <= arr[k + 1]
  {
    var j := 0;
    while j < n - 1 - i
      invariant 0 <= j <= n - 1 - i
      invariant multiset(arr[..]) == multiset(old(arr[..]))
      invariant forall k :: 0 <= k < i ==> (k < i - 1 ==> arr[k] <= arr[k + 1])
    {
      if arr[j] > arr[j + 1] {
        arr[j], arr[j + 1] := arr[j + 1], arr[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): simplified with fixed invariants and proper element tracking */
  var temp := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> temp[k] == arr[k]
  {
    temp[i] := arr[i];
    i := i + 1;
  }
  
  Sort(temp);
  
  var unique := new int[arr.Length];
  var uniqueCount := 0;
  
  if temp.Length > 0 {
    unique[0] := temp[0];
    uniqueCount := 1;
    
    i := 1;
    while i < temp.Length
      invariant 1 <= i <= temp.Length
      invariant 1 <= uniqueCount <= i
      invariant uniqueCount <= unique.Length
      invariant forall k :: 0 <= k < uniqueCount - 1 ==> unique[k] <= unique[k + 1]
      invariant forall k :: 0 <= k < uniqueCount ==> unique[k] in temp[..]
      invariant forall x :: x in temp[..i] ==> x in unique[..uniqueCount]
      invariant forall x :: x in unique[..uniqueCount] ==> x in temp[..]
    {
      if temp[i] != temp[i - 1] {
        unique[uniqueCount] := temp[i];
        uniqueCount := uniqueCount + 1;
      }
      i := i + 1;
    }
  }
  
  result := new int[uniqueCount];
  i := 0;
  while i < uniqueCount
    invariant 0 <= i <= uniqueCount
    invariant forall k :: 0 <= k < i ==> result[k] == unique[k]
  {
    result[i] := unique[i];
    i := i + 1;
  }
}
// </vc-code>
