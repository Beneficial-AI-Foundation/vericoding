// <vc-preamble>
predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Switched to binary search to prevent timeouts on large inputs. */
{
    var low: int := 0;
    var high: int := x;
    var ans: int := 0;
    while low <= high 
        invariant 0 <= low <= x + 1
        invariant -1 <= high <= x
        invariant ans * ans <= x
        invariant ans < low ==> forall k: int :: ans < k < low ==> k*k > x
        decreases high - low
    {
        var mid := low + (high - low) / 2;
        if mid > 0 && mid > x / mid { // mid*mid > x
            high := mid - 1;
        } else { // mid*mid <= x
            ans := mid;
            low := mid + 1;
        }
    }
    res := ans;
}
// </vc-code>
