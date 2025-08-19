method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
 requires 1<=x<a.Length
 requires a.Length!=0
 ensures x<=p<a.Length
 ensures forall i::0<=i<x==> a[i]<=m
 ensures exists i::0<=i<x && a[i]==m
 ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
 ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{
    /* code modified by LLM (iteration 2): Use only non-ghost variable and assign ghost at end */
    // Find the maximum in a[0..x) using non-ghost variable
    var max_val := a[0];
    var i := 1;
    while i < x
        invariant 1 <= i <= x
        invariant forall j :: 0 <= j < i ==> a[j] <= max_val
        invariant exists j :: 0 <= j < i && a[j] == max_val
    {
        if a[i] > max_val {
            max_val := a[i];
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 2): Assign ghost variable from non-ghost variable */
    m := max_val;
    
    /* code modified by LLM (iteration 2): Use non-ghost max_val in loop condition */
    // Find the first position p >= x where a[p] > max_val, or set p to a.Length-1
    var pos := x;
    while pos < a.Length - 1 && a[pos] <= max_val
        invariant x <= pos < a.Length
        invariant forall j :: x <= j < pos ==> a[j] <= max_val
    {
        pos := pos + 1;
    }
    p := pos;
}