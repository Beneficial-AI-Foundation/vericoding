//IMPL 
method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
 ensures fresh(b)
 ensures fresh(c)
 ensures a[..] == b[..] + c[..]
 ensures a.Length == b.Length + c.Length
 ensures a.Length > 1 ==> a.Length > b.Length
 ensures a.Length > 1 ==> a.Length > c.Length
{
    var mid := a.Length / 2;
    b := new int[mid];
    c := new int[a.Length - mid];
    
    /* code modified by LLM (iteration 3): Fixed mathematical assertions with proper syntax */
    assert b.Length == mid;
    assert c.Length == a.Length - mid;
    assert b.Length + c.Length == a.Length;
    
    // Establish the key length relationships when a.Length > 1
    if a.Length > 1 {
        /* code modified by LLM (iteration 3): Mathematical proof for division properties */
        assert mid == a.Length / 2;
        // For integer division: a.Length / 2 < a.Length when a.Length > 1
        assert mid < a.Length; // b.Length < a.Length
        // For the second part: a.Length - mid where mid = a.Length / 2
        // We know that a.Length / 2 >= 1 when a.Length > 1 (since a.Length >= 2)
        // So a.Length - a.Length/2 < a.Length
        assert a.Length - mid < a.Length; // c.Length < a.Length
    }
    
    var i := 0;
    while i < mid
        invariant 0 <= i <= mid
        invariant forall k :: 0 <= k < i ==> b[k] == a[k]
    {
        b[i] := a[i];
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 3): Added assertion after first loop */
    assert forall k :: 0 <= k < mid ==> b[k] == a[k];
    
    i := 0;
    while i < a.Length - mid
        invariant 0 <= i <= a.Length - mid
        invariant forall k :: 0 <= k < i ==> c[k] == a[mid + k]
    {
        c[i] := a[mid + i];
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 3): Added comprehensive assertions to establish sequence equality */
    assert forall k :: 0 <= k < c.Length ==> c[k] == a[mid + k];
    
    // Establish sequence relationships step by step
    assert b[..] == a[0..mid];
    assert c[..] == a[mid..a.Length];
    
    // Help Dafny understand sequence concatenation
    assert a[0..mid] + a[mid..a.Length] == a[0..a.Length];
    assert a[0..a.Length] == a[..];
}