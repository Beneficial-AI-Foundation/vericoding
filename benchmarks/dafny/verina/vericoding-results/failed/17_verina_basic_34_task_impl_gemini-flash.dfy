// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The problem with the `CountEvens` function is that it doesn't correctly handle slices. In Dafny, `arr[1..]` creates a new sequence, not a view of the array. To fix this, I introduce start and end indices to handle array segments, making recursions correct. */
function CountEvens(arr: array<int>, start: int, end: int): (count: int)
  requires 0 <= start <= end <= arr.Length
{
  if start == end then 0
  else (if IsEven(arr[start]) then 1 else 0) + CountEvens(arr, start + 1, end)
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
/* code modified by LLM (iteration 5): Corrected the closing brace syntax error, and updated the call to `CountEvens` to use an explicit start and end index. */
{
    var evenCount := CountEvens(arr, 0, arr.Length);
    result := new int[evenCount];
    var j := 0;
    for i := 0 to arr.Length - 1
    {
        invariant 0 <= i <= arr.Length;
        invariant 0 <= j <= evenCount;
        invariant forall k :: 0 <= k < j ==> IsEven(result[k]) && result[k] in arr[..];
        invariant forall k :: 0 <= k < j ==> exists l :: 0 <= l < i && result[k] == arr[l] && IsEven(arr[l]);
        invariant forall k :: 0 <= k < i && IsEven(arr[k]) ==> exists l :: 0 <= l < j && result[l] == arr[k];

        if IsEven(arr[i]) {
            result[j] := arr[i];
            j := j + 1;
        }
    }
    return result;
}
// </vc-code>
