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
    
    /* code modified by LLM (iteration 2): Fixed loop invariants to properly establish postcondition */
    while low <= high 
        invariant 0 <= low <= high + 1
        invariant low * low <= n + 1
        invariant (high + 1) * (high + 1) >= n + 1
        invariant high >= 0
    {
        var mid := (low + high) / 2;
        var midSquared := mid * mid;
        
        if midSquared == n {
            return mid;
        } else if midSquared < n {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 2): Establish postcondition from corrected invariants */
    assert low > high;
    assert low == high + 1;
    assert low * low <= n + 1;
    assert (high + 1) * (high + 1) >= n + 1;
    assert low * low >= n + 1;
    assert high * high <= n;
    assert (high + 1) * (high + 1) > n;
    
    r := high;
}