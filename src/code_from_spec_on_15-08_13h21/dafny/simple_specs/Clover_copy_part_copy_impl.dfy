method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
 requires src.Length >= sStart + len
 requires dest.Length >= dStart + len
 ensures r.Length == dest.Length
 ensures r[..dStart] == dest[..dStart]
 ensures r[dStart + len..] == dest[dStart + len..]
 ensures r[dStart..len+dStart] == src[sStart..len+sStart]
{
    r := new int[dest.Length];
    
    // Copy elements before dStart from dest
    var i := 0;
    while i < dStart
        invariant 0 <= i <= dStart
        invariant r[..i] == dest[..i]
    {
        r[i] := dest[i];
        i := i + 1;
    }
    
    // Copy len elements from src starting at sStart to r starting at dStart
    i := 0;
    while i < len
        invariant 0 <= i <= len
        invariant r[..dStart] == dest[..dStart]
        invariant r[dStart..dStart+i] == src[sStart..sStart+i]
    {
        r[dStart + i] := src[sStart + i];
        i := i + 1;
    }
    
    // Copy elements after dStart + len from dest
    i := dStart + len;
    while i < dest.Length
        invariant dStart + len <= i <= dest.Length
        invariant r[..dStart] == dest[..dStart]
        invariant r[dStart..dStart+len] == src[sStart..sStart+len]
        invariant r[dStart+len..i] == dest[dStart+len..i]
    {
        r[i] := dest[i];
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): Added assertion to establish that slice bounds match array bounds */
    assert i == dest.Length;
    assert r.Length == dest.Length;
    assert r[dStart+len..i] == dest[dStart+len..i];
    assert r[dStart+len..r.Length] == dest[dStart+len..dest.Length];
}