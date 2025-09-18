// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added bounds checking for EvenIndex and proper lemmas */
function CountEvens(arr: array<int>, n: int): nat
  requires 0 <= n <= arr.Length
  reads arr
{
  if n == 0 then 0
  else if IsEven(arr[n-1]) then 1 + CountEvens(arr, n-1)
  else CountEvens(arr, n-1)
}

function EvenIndex(arr: array<int>, i: int): nat
  requires 0 <= i < arr.Length
  requires IsEven(arr[i])
  reads arr
  ensures EvenIndex(arr, i) < CountEvens(arr, arr.Length)
{
  var idx := CountEvens(arr, i+1) - 1;
  CountEvensMonotonic(arr, i+1, arr.Length);
  idx
}

lemma CountEvensIncrease(arr: array<int>, n: int)
  requires 0 < n <= arr.Length
  requires IsEven(arr[n-1])
  ensures CountEvens(arr, n) == CountEvens(arr, n-1) + 1
{
}

lemma CountEvensMonotonic(arr: array<int>, i: int, j: int)
  requires 0 <= i <= j <= arr.Length
  ensures CountEvens(arr, i) <= CountEvens(arr, j)
  decreases j - i
{
  if i < j {
    CountEvensMonotonic(arr, i, j-1);
  }
}

lemma EvenIndexBounds(arr: array<int>, i: int)
  requires 0 <= i < arr.Length
  requires IsEven(arr[i])
  ensures 0 <= EvenIndex(arr, i) < CountEvens(arr, arr.Length)
{
  CountEvensMonotonic(arr, i+1, arr.Length);
}

lemma EvenIndexPreserved(arr: array<int>, i: int, j: int)
  requires 0 <= i < j < arr.Length
  requires IsEven(arr[i]) && IsEven(arr[j])
  ensures EvenIndex(arr, i) < EvenIndex(arr, j)
{
  CountEvensMonotonic(arr, i+1, j);
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
/* code modified by LLM (iteration 5): Fixed bounds checking and invariant maintenance */
{
  var count := CountEvens(arr, arr.Length);
  result := new int[count];
  
  if count == 0 {
    return;
  }
  
  var idx := 0;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= idx <= count
    invariant idx == CountEvens(arr, i)
    invariant forall j :: 0 <= j < idx ==> IsEven(result[j])
    invariant forall j :: 0 <= j < i && IsEven(arr[j]) ==> 
      0 <= EvenIndex(arr, j) < idx && result[EvenIndex(arr, j)] == arr[j]
    invariant forall j :: 0 <= j < idx ==> exists k :: 0 <= k < i && IsEven(arr[k]) && result[j] == arr[k]
    invariant forall p, q :: 0 <= p < q < i && IsEven(arr[p]) && IsEven(arr[q]) ==> 
      0 <= EvenIndex(arr, p) < EvenIndex(arr, q) < idx && 
      result[EvenIndex(arr, p)] == arr[p] && result[EvenIndex(arr, q)] == arr[q]
  {
    if IsEven(arr[i]) {
      EvenIndexBounds(arr, i);
      CountEvensMonotonic(arr, i+1, arr.Length);
      assert idx == EvenIndex(arr, i);
      assert 0 <= idx < count;
      result[idx] := arr[i];
      idx := idx + 1;
    }
    i := i + 1;
  }
  
  assert i == arr.Length;
  assert idx == count;
}
// </vc-code>
