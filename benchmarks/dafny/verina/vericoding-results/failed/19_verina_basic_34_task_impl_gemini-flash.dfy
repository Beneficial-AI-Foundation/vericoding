// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected syntax for function body. */
function CountEven(arr: array<int>): (count: int)
{
  (count k | 0 <= k < arr.Length && IsEven(arr[k]))
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
/* code modified by LLM (iteration 5): No changes needed in this code section. */
{
    var evenCount := 0;
    for i := 0 to arr.Length - 1
        invariant 0 <= i <= arr.Length
        invariant evenCount == (count k | 0 <= k < i && IsEven(arr[k]))
    {
        if IsEven(arr[i]) then
            evenCount := evenCount + 1;
    }

    result := new int[evenCount];
    var resultIndex := 0;

    for i := 0 to arr.Length - 1
        invariant 0 <= i <= arr.Length
        invariant 0 <= resultIndex <= evenCount
        invariant forall k :: 0 <= k < resultIndex ==> IsEven(result[k]) && (exists j :: 0 <= j < i && arr[j] == result[k])
        invariant forall k :: 0 <= k < i && IsEven(arr[k]) ==> (exists rk :: 0 <= rk < resultIndex && result[rk] == arr[k])
    {
        if IsEven(arr[i]) then
        {
            result[resultIndex] := arr[i];
            resultIndex := resultIndex + 1;
        }
    }
    assert resultIndex == evenCount;
}
// </vc-code>
