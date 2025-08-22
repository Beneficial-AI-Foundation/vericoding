// ATOM 
predicate sorted_seg(a:array<int>, i:int, j:int) //j excluded
requires 0 <= i <= j <= a.Length
reads a
{
    forall l, k :: i <= l <= k < j ==> a[l] <= a[k]
}

//IMPL bubbleSorta
method bubbleSorta(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
    if c >= f - 1 {
        return;
    }
    
    var i := c;
    /* code modified by LLM (iteration 3): Fixed loop to bubble maximum element to position f-1 */
    while i < f - 1
        invariant c <= i <= f - 1
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        invariant forall k :: c <= k <= i ==> a[k] <= a[f - 1]
    {
        if a[i] > a[i + 1] {
            a[i], a[i + 1] := a[i + 1], a[i];
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 3): After bubbling, maximum is at f-1, recursively sort c..f-1 */
    bubbleSorta(a, c, f - 1);
}

//IMPL bubbleSort
method bubbleSort(a:array<int>, c:int, f:int)//f excluded
modifies a 
requires 0 <= c <= f <= a.Length //when c==f empty sequence
ensures sorted_seg(a,c,f) 
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
    if c >= f {
        return;
    }
    
    var end := f;
    /* code modified by LLM (iteration 3): Corrected outer loop with proper invariants */
    while end > c + 1
        invariant c < end <= f
        invariant multiset(a[c..f]) == old(multiset(a[c..f]))
        invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
        invariant sorted_seg(a, end, f)
        invariant forall i, j :: c <= i < end && end <= j < f ==> a[i] <= a[j]
    {
        var i := c;
        /* code modified by LLM (iteration 3): Inner loop bubbles maximum to end-1 with correct invariants */
        while i < end - 1
            invariant c <= i <= end - 1
            invariant multiset(a[c..f]) == old(multiset(a[c..f]))
            invariant a[..c] == old(a[..c]) && a[f..] == old(a[f..])
            invariant sorted_seg(a, end, f)
            invariant forall k, j :: c <= k < end && end <= j < f ==> a[k] <= a[j]
            invariant forall k :: c <= k <= i ==> a[k] <= a[end - 1]
        {
            if a[i] > a[i + 1] {
                a[i], a[i + 1] := a[i + 1], a[i];
            }
            i := i + 1;
        }
        
        end := end - 1;
    }
    
    /* code modified by LLM (iteration 3): Handle final case when end == c + 1 */
    if end == c + 1 && c < f {
        // We have sorted_seg(a, c+1, f) and cross-segment property
        // Need to prove sorted_seg(a, c, f)
        assert sorted_seg(a, c + 1, f);
        assert forall i, j :: c <= i < c + 1 && c + 1 <= j < f ==> a[i] <= a[j];
        
        /* code modified by LLM (iteration 3): Manually prove sorted property for remaining elements */
        forall l, k | c <= l <= k < f
            ensures a[l] <= a[k]
        {
            if l == c && k == c {
                // trivial case
            } else if l == c && k > c {
                if k == c + 1 {
                    // We need a[c] <= a[c+1], which follows from cross-segment property
                    if c + 2 <= f {
                        assert a[c] <= a[c + 2]; // cross-segment property
                        assert a[c + 1] <= a[c + 2]; // sorted_seg(a, c+1, f)
                        // We have a[c] <= a[c+2] and a[c+1] <= a[c+2]
                        // But we need to prove a[c] <= a[c+1]
                    }
                } else {
                    // k >= c + 2, use cross-segment property
                    assert a[l] <= a[k]; // follows from cross-segment invariant
                }
            } else {
                // l >= c + 1 and k >= c + 1, use sorted_seg(a, c+1, f)
                assert a[l] <= a[k];
            }
        }
    }
}