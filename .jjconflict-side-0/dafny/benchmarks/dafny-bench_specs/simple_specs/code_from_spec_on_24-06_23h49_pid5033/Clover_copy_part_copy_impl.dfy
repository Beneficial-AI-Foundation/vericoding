//IMPL copy
method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
 requires src.Length >= sStart + len
 requires dest.Length >= dStart + len
 ensures r.Length == dest.Length
 ensures r[..dStart] == dest[..dStart]
 ensures r[dStart + len..] == dest[dStart + len..]
 ensures r[dStart..len+dStart] == src[sStart..len+sStart]
{
    r := new int[dest.Length];
    
    // Copy the prefix part of dest (before dStart)
    var i := 0;
    while i < dStart
        invariant 0 <= i <= dStart
        invariant r[..i] == dest[..i]
    {
        r[i] := dest[i];
        i := i + 1;
    }
    
    // Copy from src to the middle part
    i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant r[..dStart] == dest[..dStart]
        invariant r[dStart..dStart+i] == src[sStart..sStart+i]
        /* code modified by LLM (iteration 2): Fixed bounds invariants */
        invariant dStart + i <= r.Length
        invariant sStart + i <= src.Length
    {
        r[dStart + i] := src[sStart + i];
        i := i + 1;
    }
    
    // Copy the suffix part of dest (after dStart + len)
    i := dStart + len;
    while i < dest.Length
        invariant dStart + len <= i <= dest.Length
        invariant r[..dStart] == dest[..dStart]
        invariant r[dStart..dStart+len] == src[sStart..sStart+len]
        invariant r[dStart+len..i] == dest[dStart+len..i]
        /* code modified by LLM (iteration 2): Fixed bounds invariant */
        invariant i <= r.Length
    {
        r[i] := dest[i];
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 2): Simplified final assertions */
    assert r[..dStart] == dest[..dStart];
    assert r[dStart..dStart+len] == src[sStart..sStart+len];
    assert r[dStart+len..] == dest[dStart+len..];
}