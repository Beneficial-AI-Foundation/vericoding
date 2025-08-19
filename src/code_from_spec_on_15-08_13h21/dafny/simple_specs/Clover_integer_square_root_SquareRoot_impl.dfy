//IMPL 
method SquareRoot(N:nat) returns (r:nat)
 ensures r*r <= N < (r+1)*(r+1)
{
    if N == 0 {
        return 0;
    }
    
    var low := 0;
    var high := N;
    
    /* code modified by LLM (iteration 1): Fixed loop invariants and termination condition for binary search */
    while low < high
        invariant 0 <= low <= high <= N
        invariant low == 0 || (low - 1) * (low - 1) <= N
        invariant N < (high + 1) * (high + 1)
    {
        /* code modified by LLM (iteration 1): Use mid + 1 to ensure progress and avoid infinite loop */
        var mid := low + (high - low) / 2;
        var midSquared := mid * mid;
        
        if midSquared <= N {
            /* code modified by LLM (iteration 1): Check if mid could be the answer before updating */
            if (mid + 1) * (mid + 1) > N {
                r := mid;
                return;
            }
            low := mid + 1;
        } else {
            high := mid;
        }
    }
    
    /* code modified by LLM (iteration 1): Handle the case when loop exits with low == high */
    if low * low <= N {
        r := low;
    } else {
        r := low - 1;
    }
}