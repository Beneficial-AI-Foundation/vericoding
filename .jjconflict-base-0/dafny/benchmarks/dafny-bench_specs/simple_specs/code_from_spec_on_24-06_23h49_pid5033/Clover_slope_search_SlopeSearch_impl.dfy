//IMPL SlopeSearch
method SlopeSearch(a: array2<int>, key: int) returns (m:int, n:int)
 requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
 requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
 requires exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a[i,j]==key
 ensures 0<=m<a.Length0 && 0<=n<a.Length1
 ensures a[m,n]==key
{
    var i := 0;
    var j := a.Length1 - 1;
    
    /* code modified by LLM (iteration 2): Simplified loop with correct invariants that maintain the existence of key in searchable region */
    while a[i,j] != key
        invariant 0 <= i < a.Length0 && 0 <= j < a.Length1
        invariant exists i',j' :: i<=i'<a.Length0 && 0<=j'<=j && a[i',j']==key
        decreases a.Length0 - i + j
    {
        if a[i,j] > key {
            j := j - 1;
        } else {
            i := i + 1;
        }
    }
    
    m := i;
    n := j;
}