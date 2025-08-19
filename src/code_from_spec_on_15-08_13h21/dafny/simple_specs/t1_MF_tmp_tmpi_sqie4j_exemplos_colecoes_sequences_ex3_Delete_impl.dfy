//IMPL 
method Delete(line:array<char>, l:nat, at:nat, p:nat)
 requires l <= line.Length
 requires at+p <= l
 modifies line
 ensures line[..at] == old(line[..at])
 ensures line[at..l-p] == old(line[at+p..l])
{
    /* code modified by LLM (iteration 1): Fixed loop invariants to properly track the shifting operation and handle array bounds correctly */
    var i := at;
    while i < l - p
        invariant at <= i <= l - p
        invariant line[..at] == old(line[..at])
        invariant line[at..i] == old(line[at+p..at+p+(i-at)])
        invariant forall k :: i <= k < l - p ==> line[k] == old(line[k])
        invariant forall k :: l - p <= k < l ==> line[k] == old(line[k])
    {
        line[i] := line[i + p];
        i := i + 1;
    }
}