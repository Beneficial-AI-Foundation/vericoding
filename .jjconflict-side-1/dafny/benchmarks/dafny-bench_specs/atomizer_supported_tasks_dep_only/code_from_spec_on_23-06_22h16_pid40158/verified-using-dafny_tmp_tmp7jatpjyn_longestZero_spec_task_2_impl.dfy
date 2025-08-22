// ATOM 
function getSize(i: int, j:int) : int
{
    j - i + 1    
}

//IMPL longestZero
method longestZero(a: array<int>) returns (sz:int, pos:int)   
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i:int  :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
    /* code modified by LLM (iteration 1): Initialize with valid defaults */
    sz := 0;
    pos := 0;
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= sz <= a.Length
        invariant 0 <= pos < a.Length
        invariant pos + sz <= a.Length
        invariant forall k:int :: pos <= k < pos + sz ==> a[k] == 0
        /* code modified by LLM (iteration 1): Simplified invariant for processed segments */
        invariant forall start, end :: (0 <= start <= end < i && end - start + 1 > sz) ==> exists k :: start <= k <= end && a[k] != 0
    {
        if a[i] == 0 {
            var currentStart := i;
            var j := i;
            
            /* code modified by LLM (iteration 1): Count consecutive zeros */
            while j < a.Length && a[j] == 0
                invariant i <= j <= a.Length
                invariant currentStart == i
                invariant forall k :: currentStart <= k < j ==> a[k] == 0
            {
                j := j + 1;
            }
            
            var currentSize := j - currentStart;
            
            /* code modified by LLM (iteration 1): Update if we found a longer sequence */
            if currentSize > sz {
                sz := currentSize;
                pos := currentStart;
            }
            
            /* code modified by LLM (iteration 1): Skip past processed zeros */
            i := j;
        } else {
            i := i + 1;
        }
    }
    
    /* code modified by LLM (iteration 1): Final assertion to help verification */
    assert forall start, end :: (0 <= start <= end < a.Length && end - start + 1 > sz) ==> exists k :: start <= k <= end && a[k] != 0;
}

//IMPL Main  
method Main()
{
}