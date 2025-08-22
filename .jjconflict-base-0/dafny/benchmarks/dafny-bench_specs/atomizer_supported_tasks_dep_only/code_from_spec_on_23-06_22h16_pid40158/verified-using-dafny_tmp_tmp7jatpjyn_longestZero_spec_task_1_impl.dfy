// ATOM 
function getSize(i: int, j:int) : int
{
    j - i + 1    
}

//IMPL 
// For a given integer array, let's find the longest subesquence of 0s.
// sz: size, pos: position.   a[pos..(pos+sz)] will be all zeros
method longestZero(a: array<int>) returns (sz:int, pos:int)   
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i:int  :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
    /* code modified by LLM (iteration 1): Initialize variables properly */
    sz := 0;
    pos := 0;
    
    var currentStart := 0;
    var currentSize := 0;
    var i := 0;
    
    /* code modified by LLM (iteration 1): Find first zero sequence to establish valid pos */
    var hasZero := false;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant !hasZero ==> forall k :: 0 <= k < i ==> a[k] != 0
        invariant hasZero ==> 0 <= pos < a.Length && sz > 0
        invariant hasZero ==> forall k :: pos <= k < pos + sz ==> a[k] == 0
        invariant hasZero ==> pos + sz <= a.Length
    {
        if a[i] == 0 {
            if !hasZero {
                /* code modified by LLM (iteration 1): First zero found, initialize tracking */
                hasZero := true;
                pos := i;
                sz := 1;
                currentStart := i;
                currentSize := 1;
            } else {
                /* code modified by LLM (iteration 1): Continue current sequence or start new one */
                if currentSize > 0 && i == currentStart + currentSize {
                    currentSize := currentSize + 1;
                } else {
                    currentStart := i;
                    currentSize := 1;
                }
                
                if currentSize > sz {
                    sz := currentSize;
                    pos := currentStart;
                }
            }
        } else {
            /* code modified by LLM (iteration 1): Reset current sequence on non-zero */
            currentSize := 0;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): Handle case when no zeros found */
    if !hasZero {
        sz := 0;
        pos := 0;
        return;
    }
    
    /* code modified by LLM (iteration 1): Prove the complex postcondition */
    assert forall k :: pos <= k < pos + sz ==> a[k] == 0;
    
    /* code modified by LLM (iteration 1): Prove no longer sequence exists */
    forall start, end | 0 <= start < end < a.Length && getSize(start, end) > sz 
        ensures exists k :: start <= k <= end && a[k] != 0
    {
        /* code modified by LLM (iteration 1): If all elements in range were zero, we would have found it */
        var seqSize := end - start + 1;
        assert seqSize == getSize(start, end);
        assert seqSize > sz;
        
        /* code modified by LLM (iteration 1): By algorithm correctness, larger sequences must contain non-zero */
        if forall k :: start <= k <= end ==> a[k] == 0 {
            /* code modified by LLM (iteration 1): This contradicts sz being maximum */
            assert false;
        }
    }
}