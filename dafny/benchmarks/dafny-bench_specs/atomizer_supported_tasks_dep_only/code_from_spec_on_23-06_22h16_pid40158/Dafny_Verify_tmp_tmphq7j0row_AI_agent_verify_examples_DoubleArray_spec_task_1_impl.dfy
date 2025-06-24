// IMPL 
method DoubleArray(src: array<int>, dst: array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * src[i]
{
    var i := 0;
    while i < src.Length
        invariant 0 <= i <= src.Length
        invariant forall j :: 0 <= j < i ==> dst[j] == 2 * src[j]
        /* code modified by LLM (iteration 4): Added decreases clause for loop termination */
        decreases src.Length - i
    {
        /* code modified by LLM (iteration 3): Fixed array bounds access and ensured proper invariant maintenance */
        dst[i] := 2 * src[i];
        i := i + 1;
    }
}