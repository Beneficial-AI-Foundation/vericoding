//IMPL 
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
    
    /* code modified by LLM (iteration 1): strengthened loop invariants to maintain proper bounds for square root property */
    while low <= high
        invariant 0 <= low <= high + 1 <= n + 1
        invariant low > 0 ==> (low - 1) * (low - 1) <= n
        invariant high < n ==> (high + 1) * (high + 1) > n
        invariant low <= high + 1
    {
        var mid := (low + high) / 2;
        var midSquared := mid * mid;
        
        if midSquared == n {
            r := mid;
            return;
        } else if midSquared < n {
            /* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance */
            assert mid * mid < n;
            low := mid + 1;
        } else {
            /* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance */
            assert mid * mid > n;
            high := mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 1): added assertions to justify that high satisfies the postcondition */
    assert low > high;
    assert low > 0 ==> (low - 1) * (low - 1) <= n;
    assert high < n ==> (high + 1) * (high + 1) > n;
    assert high >= 0;
    assert high * high <= n;
    assert (high + 1) * (high + 1) > n;
    r := high;
}