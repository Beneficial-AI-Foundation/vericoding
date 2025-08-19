//IMPL
method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
 ensures fresh(b)
 ensures fresh(c)
 ensures a[..] == b[..] + c[..]
 ensures a.Length == b.Length + c.Length
 ensures a.Length > 1 ==> a.Length > b.Length
 ensures a.Length > 1 ==> a.Length > c.Length
{
    var splitPoint := a.Length / 2;
    
    b := new int[splitPoint];
    c := new int[a.Length - splitPoint];
    
    var i := 0;
    while i < splitPoint
        invariant 0 <= i <= splitPoint
        invariant forall j :: 0 <= j < i ==> b[j] == a[j]
    {
        b[i] := a[i];
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to establish b[..] == a[..splitPoint] */
    assert b[..] == a[..splitPoint];
    
    i := 0;
    while i < c.Length
        invariant 0 <= i <= c.Length
        invariant forall j :: 0 <= j < i ==> c[j] == a[splitPoint + j]
        /* code modified by LLM (iteration 1): added invariant to maintain b[..] == a[..splitPoint] */
        invariant b[..] == a[..splitPoint]
    {
        c[i] := a[splitPoint + i];
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertions to help prove the concatenation postcondition */
    assert c[..] == a[splitPoint..];
    assert a[..] == a[..splitPoint] + a[splitPoint..];
    assert a[..] == b[..] + c[..];
}