//IMPL
method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
 requires 1<=x<a.Length
 requires a.Length!=0
 ensures x<=p<a.Length
 ensures forall i::0<=i<x==> a[i]<=m
 ensures exists i::0<=i<x && a[i]==m
 ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
 ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{
    // Find the maximum in the prefix a[0..x)
    /* code modified by LLM (iteration 4): fixed initial invariant establishment */
    m := a[0];
    var i := 1;
    ghost var maxIndex := 0;
    while i < x
        invariant 1 <= i <= x
        invariant forall j :: 0 <= j < i ==> a[j] <= m
        invariant exists j :: 0 <= j < i && a[j] == m
        invariant 0 <= maxIndex < i && a[maxIndex] == m
    {
        if a[i] > m {
            m := a[i];
            maxIndex := i;
        }
        i := i + 1;
    }
    
    // Find the first position p >= x where a[p] > m, or set p to a.Length-1
    /* code modified by LLM (iteration 4): corrected loop to properly handle the search logic */
    p := x;
    while p < a.Length - 1 && a[p] <= m
        invariant x <= p < a.Length
        invariant forall j :: x <= j < p ==> a[j] <= m
    {
        p := p + 1;
    }
    
    /* code modified by LLM (iteration 4): simplified verification logic */
    // At this point, either p == a.Length-1 or a[p] > m
    
    // Fourth postcondition verification
    if x <= p < a.Length - 1 {
        // We must have exited the loop because a[p] > m (not because p reached a.Length-1)
        assert a[p] > m;
        // From loop invariant: all elements from x to p-1 are <= m
        assert forall j :: x <= j < p ==> a[j] <= m;
        // From first loop: all elements from 0 to x-1 are <= m
        assert forall i :: 0 <= i < x ==> a[i] <= m;
        // Combine both ranges
        assert forall i :: 0 <= i < p ==> a[i] <= m;
        assert forall i :: 0 <= i < p ==> a[i] < a[p];
    }
}