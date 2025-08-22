//IMPL Delete
method Delete(line:array<char>, l:nat, at:nat, p:nat)
 requires l <= line.Length
 requires at+p <= l
 modifies line
 ensures line[..at] == old(line[..at])
 ensures line[at..l-p] == old(line[at+p..l])
{
    var i := at;
    /* code modified by LLM (iteration 1): Fixed loop invariants and bounds to ensure verification */
    while i < l - p
        invariant at <= i <= l - p
        invariant line[..at] == old(line[..at])
        invariant line[at..i] == old(line[at+p..at+p+(i-at)])
        invariant forall k :: i <= k < l ==> line[k] == old(line[k])
        invariant i + p <= l
    {
        /* code modified by LLM (iteration 1): Added bounds assertion for array access safety */
        assert i + p < line.Length;
        line[i] := line[i + p];
        i := i + 1;
    }
}