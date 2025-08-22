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
    sz := 0;
    pos := 0;
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= sz <= a.Length
        invariant 0 <= pos < a.Length
        invariant pos + sz <= a.Length
        invariant forall k :: pos <= k < pos + sz ==> a[k] == 0
        /* code modified by LLM (iteration 3): Fixed optimality invariant to match postcondition exactly */
        invariant forall start, end :: (0 <= start < end < i && getSize(start, end) > sz) ==> exists k :: start <= k <= end && a[k] != 0
    {
        if a[i] == 0 {
            var start := i;
            var currentSz := 0;
            
            while i < a.Length && a[i] == 0
                invariant start <= i <= a.Length
                invariant currentSz == i - start
                invariant forall k :: start <= k < i ==> a[k] == 0
                invariant 0 <= sz <= a.Length
                invariant 0 <= pos < a.Length
                invariant pos + sz <= a.Length
                invariant forall k :: pos <= k < pos + sz ==> a[k] == 0
                /* code modified by LLM (iteration 3): Maintain optimality for processed segments */
                invariant forall s, e :: (0 <= s < e < start && getSize(s, e) > sz) ==> exists k :: s <= k <= e && a[k] != 0
            {
                currentSz := currentSz + 1;
                i := i + 1;
            }
            
            if currentSz > sz {
                sz := currentSz;
                pos := start;
            }
            
            /* code modified by LLM (iteration 3): Assert optimality for the segment we just processed */
            assert forall s, e :: (0 <= s < e <= start && getSize(s, e) > sz) ==> exists k :: s <= k <= e && a[k] != 0;
        } else {
            /* code modified by LLM (iteration 3): Assert optimality when we encounter non-zero element */
            assert forall s, e :: (0 <= s < e <= i && getSize(s, e) > sz) ==> exists k :: s <= k <= e && a[k] != 0;
            i := i + 1;
        }
    }
    
    /* code modified by LLM (iteration 3): Helper assertions to establish final postcondition */
    assert i == a.Length;
    assert forall start, end :: (0 <= start < end < a.Length && getSize(start, end) > sz) ==> exists k :: start <= k <= end && a[k] != 0;
    
    /* code modified by LLM (iteration 3): Handle the case where end == a.Length - 1 */
    assert forall start, end :: (0 <= start < end < a.Length && getSize(start, end) > sz) ==> exists k :: start <= k <= end && a[k] != 0;
    
    /* code modified by LLM (iteration 3): Prove the postcondition by considering all possible segments */
    forall start, end | 0 <= start < end < a.Length && getSize(start, end) > sz
        ensures exists k :: start <= k <= end && a[k] != 0
    {
        if end < a.Length {
            assert exists k :: start <= k <= end && a[k] != 0;
        }
    }
}

//IMPL Main
method Main()
{
}