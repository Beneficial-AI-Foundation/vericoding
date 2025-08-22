//ATOM_PLACEHOLDER_mroot1


//ATOM_PLACEHOLDER_mroot2

//IMPL mroot3
method mroot3(n:int) returns (r:int) //Cost O(log n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    if n == 0 {
        r := 0;
        return;
    }
    
    var low := 0;
    var high := n;
    
    // Binary search for the square root
    while low <= high
        /* code modified by LLM (iteration 1): Fixed invariants to properly maintain bounds during binary search */
        invariant 0 <= low <= high + 1
        invariant low == 0 || (low - 1) * (low - 1) <= n
        invariant high == n || (high + 1) * (high + 1) > n
        decreases high - low
    {
        var mid := (low + high) / 2;
        var midSquared := mid * mid;
        
        if midSquared == n {
            r := mid;
            return;
        } else if midSquared < n {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 1): Added assertion to help prove the postcondition */
    assert low > high;
    assert low - 1 <= high;
    assert (low - 1) * (low - 1) <= n;
    assert low * low > n;
    
    r := high;
}