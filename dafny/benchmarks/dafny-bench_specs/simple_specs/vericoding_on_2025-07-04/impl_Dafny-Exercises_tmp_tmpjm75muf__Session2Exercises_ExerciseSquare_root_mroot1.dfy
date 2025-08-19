//IMPL 
method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    if n == 0 {
        return 0;
    }
    
    var low := 0;
    var high := n;
    
    /* code modified by LLM (iteration 1): Fixed loop invariants to properly maintain bounds and added termination condition */
    while low < high
        invariant 0 <= low <= high <= n
        invariant low * low <= n
        invariant (high + 1) * (high + 1) > n || high == n
        decreases high - low
    {
        /* code modified by LLM (iteration 1): Changed mid calculation to avoid infinite loops */
        var mid := low + (high - low) / 2;
        var midSquared := mid * mid;
        
        if midSquared <= n {
            /* code modified by LLM (iteration 1): Check if mid+1 squared exceeds n to find exact answer */
            if (mid + 1) * (mid + 1) > n {
                r := mid;
                return;
            }
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 1): Added assertion to help verify postcondition */
    assert low == high;
    assert low * low <= n;
    assert (low + 1) * (low + 1) > n;
    r := low;
}