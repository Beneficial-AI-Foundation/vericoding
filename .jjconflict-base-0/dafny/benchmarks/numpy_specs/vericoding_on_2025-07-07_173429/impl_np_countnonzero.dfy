//IMPL nonzero
/* code modified by LLM (iteration 3): added helper predicate to count non-zero elements */
predicate IsNonZero(arr: array<real>, index: int)
    reads arr
    requires 0 <= index < arr.Length
{
    arr[index] != 0.0
}

function CountNonZeros(arr: array<real>, upTo: int): int
    reads arr
    requires 0 <= upTo <= arr.Length
{
    if upTo == 0 then 0
    else CountNonZeros(arr, upTo - 1) + (if arr[upTo - 1] != 0.0 then 1 else 0)
}

method nonzero(arr: array<real>) returns (num: int)
    requires arr.Length >= 0
    ensures num >= 0
{
    num := 0;
    var i := 0;
    /* code modified by LLM (iteration 3): updated loop invariant to use helper function */
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant num >= 0
        invariant num == CountNonZeros(arr, i)
    {
        if arr[i] != 0.0 {
            num := num + 1;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 3): updated assertion to use helper function */
    assert i == arr.Length;
    assert num == CountNonZeros(arr, arr.Length);
}