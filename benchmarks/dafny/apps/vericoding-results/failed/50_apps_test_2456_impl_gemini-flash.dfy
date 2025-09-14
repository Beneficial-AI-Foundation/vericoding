predicate ValidInput(n: int, r: int)
{
    n >= 1 && r >= 1
}

function ExpectedResult(n: int, r: int): int
    requires ValidInput(n, r)
{
    var k := if r < n - 1 then r else n - 1;
    k * (k + 1) / 2 + (if r >= n then 1 else 0)
}

// <vc-helpers>
function countPairs(n: int, r: int, k: int): int
    requires n >= 1 && r >= 1 && k >= 0
    decreases k
{
    if k == 0 then 0
    else 
        var diff := r - k;
        var max_val := n - 1;
        var current_count := 0;
        if diff >= 0 && diff <= max_val then
            current_count := 1
        else
            current_count := 0;  // This line is now redundant but kept for clarity following previous attempts.
        
        current_count + countPairs(n, r, k - 1)
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    var count := 0;
    var k_loop := n - 1; 

    while k_loop >= 1
        decreases k_loop
        invariant k_loop >= 0
        invariant count == (countPairs(n, r, n - 1) - countPairs(n, r, k_loop))
    {
        var diff := r - k_loop;
        if diff >= 0 && diff <= n - 1
        {
            count := count + 1;
        }
        k_loop := k_loop - 1;
    }

    if r >= n
    {
        count := count + 1;
    }

    return count;
}
// </vc-code>

