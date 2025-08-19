//IMPL 
method mroot3(n:int) returns (r:int) //Cost O(log n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    if n == 0 {
        return 0;
    }
    
    var low := 0;
    var high := n;
    
    while low <= high 
    /* code modified by LLM (iteration 1): Fixed invariants to properly track binary search bounds for square root */
    invariant 0 <= low <= high + 1
    invariant high < n + 1
    invariant low == 0 || (low - 1) * (low - 1) <= n
    invariant (high + 1) * (high + 1) > n
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
    
    r := high;
}