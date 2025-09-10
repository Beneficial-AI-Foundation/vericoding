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
        var count := 0;
        if diff >= 0 && diff <= max_val then
            count := 1;
        
        count + countPairs(n, r, k - 1)
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
    var count := 0;
    var k := n - 1; 

    while k >= 1
        decreases k
        invariant k >= 0
        invariant count == countPairs(n, r, n - 1 - k)
    {
        var diff := r - k;
        if diff >= 0 && diff <= n - 1
        {
            count := count + 1;
        }
        k := k - 1;
    }

    if r >= n
    {
        count := count + 1;
    }

    return count;
}
// </vc-code>

