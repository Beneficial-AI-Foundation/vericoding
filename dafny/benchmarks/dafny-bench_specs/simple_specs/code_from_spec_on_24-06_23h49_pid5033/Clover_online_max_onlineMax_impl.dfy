//IMPL 
/* code modified by LLM (iteration 4): Moved helper function outside method */
function allPrevSmaller(a: array<int>, pos: int): bool
    reads a
    requires 0 <= pos < a.Length
{
    forall k :: 0 <= k < pos ==> a[k] < a[pos]
}

method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
 requires 1<=x<a.Length
 requires a.Length!=0
 ensures x<=p<a.Length
 ensures forall i::0<=i<x==> a[i]<=m
 ensures exists i::0<=i<x && a[i]==m
 ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
 ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{
    /* code modified by LLM (iteration 4): Fixed maximum finding loop initialization and invariants */
    // Find the maximum in a[0..x)
    m := a[0];
    var i := 1;
    while i < x
        invariant 1 <= i <= x
        invariant forall j :: 0 <= j < i ==> a[j] <= m
        invariant exists j :: 0 <= j < i && a[j] == m
    {
        if a[i] > m {
            m := a[i];
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Improved position finding logic with correct invariants */
    // Find the position p
    p := x;
    while p < a.Length - 1
        invariant x <= p < a.Length
        invariant forall j :: x <= j < p ==> (a[j] <= m || exists k :: 0 <= k < j && a[k] >= a[j])
        invariant forall j :: x <= j < p ==> (a[j] > m ==> exists k :: 0 <= k < j && a[k] >= a[j])
    {
        /* code modified by LLM (iteration 4): Simplified condition check */
        if a[p] > m {
            // Check if all previous elements are smaller
            var allSmaller := true;
            var k := 0;
            while k < p
                invariant 0 <= k <= p
                invariant allSmaller <==> (forall j :: 0 <= j < k ==> a[j] < a[p])
            {
                if a[k] >= a[p] {
                    allSmaller := false;
                    break;
                }
                k := k + 1;
            }
            
            if allSmaller {
                /* code modified by LLM (iteration 4): Added verification assertions before return */
                assert x <= p < a.Length - 1;
                assert forall j :: 0 <= j < p ==> a[j] < a[p];
                return;
            }
        }
        p := p + 1;
    }
    
    /* code modified by LLM (iteration 4): Final position verification */
    // At this point p == a.Length - 1
    assert p == a.Length - 1;
    assert x <= p < a.Length;
}