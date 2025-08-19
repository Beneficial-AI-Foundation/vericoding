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
    /* code modified by LLM (iteration 4): Compute maximum in non-ghost context first, then assign to ghost variable */
    
    // Compute the maximum in the prefix a[0..x) - this is non-ghost computation
    var max_val := a[0];
    var i_non_ghost := 1;
    while i_non_ghost < x
        invariant 1 <= i_non_ghost <= x
        invariant forall j :: 0 <= j < i_non_ghost ==> a[j] <= max_val
        invariant exists j :: 0 <= j < i_non_ghost && a[j] == max_val
    {
        if a[i_non_ghost] > max_val {
            max_val := a[i_non_ghost];
        }
        i_non_ghost := i_non_ghost + 1;
    }
    
    /* code modified by LLM (iteration 4): Assign non-ghost max_val to ghost variable m */
    m := max_val;
    
    // Find the first position >= x where a[j] > max_val
    var i := x;
    while i < a.Length
        invariant x <= i <= a.Length
        invariant forall j :: x <= j < i ==> a[j] <= max_val
    {
        if a[i] > max_val {
            break;
        }
        i := i + 1;
    }
    
    if i < a.Length {
        // Found a position where a[i] > max_val
        p := i;
    } else {
        // No position found where a[j] > max_val for j >= x
        p := a.Length - 1;
    }
}