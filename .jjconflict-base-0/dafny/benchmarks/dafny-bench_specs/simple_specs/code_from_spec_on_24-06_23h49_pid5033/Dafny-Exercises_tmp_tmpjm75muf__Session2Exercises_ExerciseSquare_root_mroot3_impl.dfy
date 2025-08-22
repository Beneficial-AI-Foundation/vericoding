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
    
    /* code modified by LLM (iteration 1): strengthened loop invariants to maintain postcondition properties */
    while low <= high
        invariant 0 <= low <= high + 1
        invariant low > 0 ==> (low - 1) * (low - 1) <= n
        invariant (high + 1) * (high + 1) > n
        invariant high >= 0
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
    
    /* code modified by LLM (iteration 1): changed final assignment and added assertion to ensure postcondition */
    assert low > high;  // loop terminated because low > high
    assert low > 0;     // since we handled n == 0 case separately
    r := low - 1;
    
    /* code modified by LLM (iteration 1): added assertions to help verify postcondition */
    assert r * r <= n;  // from invariant: (low - 1) * (low - 1) <= n
    assert (r + 1) * (r + 1) > n;  // from invariant: low * low > n, and r + 1 = low
}