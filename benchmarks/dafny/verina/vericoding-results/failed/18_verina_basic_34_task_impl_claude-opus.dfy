// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
function CountEvens(arr: array<int>): nat
  reads arr
{
  CountEvensInRange(arr, 0, arr.Length)
}

function CountEvensInRange(arr: array<int>, start: nat, end: nat): nat
  requires start <= end <= arr.Length
  reads arr
  decreases end - start
{
  if start >= end then 0
  else if IsEven(arr[start]) then 1 + CountEvensInRange(arr, start + 1, end)
  else CountEvensInRange(arr, start + 1, end)
}

lemma CountEvensInRangeProperties(arr: array<int>, start: nat, mid: nat, end: nat)
  requires start <= mid <= end <= arr.Length
  ensures CountEvensInRange(arr, start, end) == CountEvensInRange(arr, start, mid) + CountEvensInRange(arr, mid, end)
  decreases end - start
{
  if start >= mid {
  } else if IsEven(arr[start]) {
    CountEvensInRangeProperties(arr, start + 1, mid, end);
  } else {
    CountEvensInRangeProperties(arr, start + 1, mid, end);
  }
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (result: array<int>)
    ensures forall x :: x in result[..] ==> IsEven(x) && x in arr[..]
    ensures forall x :: x in arr[..] && IsEven(x) ==> x in result[..]
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i <= j 
        && IsEven(arr[i]) && IsEven(arr[j]) ==> 
        exists ri, rj :: 0 <= ri < result.Length && 0 <= rj < result.Length 
            && ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
// </vc-spec>
// <vc-code>
{
  var count := CountEvens(arr);
  result := new int[count];
  
  if count == 0 {
    return;
  }
  
  var idx := 0;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= idx <= count
    invariant idx == CountEvensInRange(arr, 0, i)
    invariant forall j :: 0 <= j < idx ==> result[j] in arr[..i] && IsEven(result[j])
    invariant forall x :: x in arr[..i] && IsEven(x) ==> x in result[..idx]
    invariant forall j, k :: 0 <= j < i && 0 <= k < i && j <= k && IsEven(arr[j]) && IsEven(arr[k]) ==>
      exists rj, rk :: 0 <= rj < idx && 0 <= rk < idx && rj <= rk && result[rj] == arr[j] && result[rk] == arr[k]
  {
    if IsEven(arr[i]) {
      result[idx] := arr[i];
      idx := idx + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
