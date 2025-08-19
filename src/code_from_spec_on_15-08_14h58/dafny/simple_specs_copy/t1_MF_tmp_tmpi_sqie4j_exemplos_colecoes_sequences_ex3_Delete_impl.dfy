//IMPL
method Delete(line:array<char>, l:nat, at:nat, p:nat)
 requires l <= line.Length
 requires at+p <= l
 modifies line
 ensures line[..at] == old(line[..at])
 ensures line[at..l-p] == old(line[at+p..l])
{
    var i := 0;
    while i < l - p - at
        invariant 0 <= i <= l - p - at
        invariant line[..at] == old(line[..at])
        invariant line[at..at+i] == old(line[at+p..at+p+i])
        invariant line[at+i..] == old(line[at+i..])
    {
        line[at + i] := line[at + p + i];
        i := i + 1;
    }
}