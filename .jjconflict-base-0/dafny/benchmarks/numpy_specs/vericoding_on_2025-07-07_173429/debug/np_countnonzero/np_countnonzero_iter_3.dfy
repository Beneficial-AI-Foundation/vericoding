//IMPL nonzero
method nonzero(arr: array<real>) returns (num: int)
    requires arr.Length >= 0
    ensures num >= 0
{
    num := 0;
    var i := 0;
    /* code modified by LLM (iteration 2): added proper loop invariant to track non-zero count */
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant num >= 0
        invariant num == |set j | 0 <= j < i && arr[j] != 0.0|
    {
        if arr[i] != 0.0 {
            num := num + 1;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 2): added assertion to help verify postcondition */
    assert i == arr.Length;
    assert num == |set j | 0 <= j < arr.Length && arr[j] != 0.0|;
}