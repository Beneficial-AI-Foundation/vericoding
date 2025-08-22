//IMPL mroot1
method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r := 0;
    /* code modified by LLM (iteration 3): Fixed loop condition and invariant to ensure postcondition */
    while (r+1)*(r+1) <= n
        invariant r >= 0
        invariant r*r <= n
        invariant (r+1)*(r+1) > n ==> r*r <= n < (r+1)*(r+1)
    {
        r := r + 1;
    }
}

//IMPL mroot2
method mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r := 0;
    var i := 0;
    /* code modified by LLM (iteration 3): Fixed algorithm to properly find square root with O(n) complexity */
    while i < n && (r+1)*(r+1) <= n
        invariant r >= 0
        invariant r*r <= n
        invariant i >= 0
        invariant i <= n
        invariant (r+1)*(r+1) > n ==> r*r <= n < (r+1)*(r+1)
    {
        if (r+1)*(r+1) <= n {
            r := r + 1;
        }
        i := i + 1;
    }
}

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
    var high := n + 1;
    
    /* code modified by LLM (iteration 3): Implemented proper binary search for square root */
    while low + 1 < high
        invariant 0 <= low < high
        invariant low * low <= n
        invariant high * high > n
    {
        var mid := low + (high - low) / 2;
        
        if mid * mid <= n {
            low := mid;
        } else {
            high := mid;
        }
    }
    
    /* code modified by LLM (iteration 3): Set result to the largest integer whose square is <= n */
    r := low;
}