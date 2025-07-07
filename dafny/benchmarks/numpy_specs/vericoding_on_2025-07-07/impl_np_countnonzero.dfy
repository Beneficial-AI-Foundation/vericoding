//IMPL
method nonzero(arr: array<real>) returns (num: int)
    requires arr.Length >= 0
    ensures num >= 0
    /* code modified by LLM (iteration 1): removed invalid recursive ensures clause that used array slicing syntax not supported in Dafny */
    ensures num <= arr.Length
{
    num := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant num >= 0
        /* code modified by LLM (iteration 1): added invariant to track that num counts non-zero elements seen so far */
        invariant num <= i
        /* code modified by LLM (iteration 4): fixed set comprehension syntax - use :: as separator in Dafny */
        invariant num == |set j :: 0 <= j < i && arr[j] != 0.0|
    {
        if arr[i] != 0.0 {
            num := num + 1;
        }
        i := i + 1;
    }
}