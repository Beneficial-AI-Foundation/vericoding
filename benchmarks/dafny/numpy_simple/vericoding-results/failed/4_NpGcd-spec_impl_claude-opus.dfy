// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplified to avoid timeout issues */
function abs(x: int): int
{
    if x < 0 then -x else x
}

function gcd(a: nat, b: nat): nat
    ensures gcd(a, b) > 0
    decreases b
{
    if a == 0 && b == 0 then 1
    else if b == 0 then a 
    else gcd(b, a % b)
}
// </vc-helpers>

// <vc-spec>
method GcdInt(a: int, b: int) returns (result: int)
    ensures
        result > 0 &&
        a % result == 0 &&
        b % result == 0 &&
        (forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Direct iterative implementation without complex lemmas */
{
    var a' := abs(a);
    var b' := abs(b);
    
    if a' == 0 && b' == 0 {
        result := 1;
        return;
    }
    
    var x := a';
    var y := b';
    
    // Compute GCD using Euclidean algorithm
    while y != 0
        invariant x >= 0 && y >= 0
        invariant x > 0 || y > 0
        invariant forall d :: d > 0 && a' % d == 0 && b' % d == 0 ==> 
                    (x % d == 0 && y % d == 0)
        invariant forall d :: d > 0 && x % d == 0 && y % d == 0 ==> 
                    (a' % d == 0 && b' % d == 0)
        decreases y
    {
        var temp := x % y;
        x := y;
        y := temp;
    }
    
    result := x;
    
    // Verify postconditions
    assert y == 0;
    assert x > 0;
    assert result > 0;
    
    // Result divides both a and b
    assert a' % result == 0;
    assert b' % result == 0;
    assert a % result == 0;
    assert b % result == 0;
    
    // Result is the greatest common divisor
    assert forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= result;
}
// </vc-code>
