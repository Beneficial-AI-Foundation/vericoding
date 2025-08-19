//IMPL 
method SquareRoot(N:nat) returns (r:nat)
 ensures r*r <= N < (r+1)*(r+1)
{
    if N == 0 {
        return 0;
    }
    
    var low := 0;
    var high := N;
    
    while low < high
        invariant 0 <= low <= high
        invariant low * low <= N
        invariant N < (high + 1) * (high + 1)
    {
        var mid := (low + high + 1) / 2;
        
        if mid * mid <= N {
            low := mid;
        } else {
            high := mid - 1;
        }
    }
    
    return low;
}