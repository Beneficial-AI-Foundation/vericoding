// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use standard Euclidean algorithm approach without negative handling in main function */
function gcd(x: int, y: int): int
    requires x >= 0 && y >= 0
    requires x > 0 || y > 0
    decreases y
{
    if y == 0 then x else gcd(y, x % y)
}

lemma GcdDivides(x: int, y: int)
    requires x >= 0 && y >= 0
    requires x > 0 || y > 0
    ensures var g := gcd(x, y); g > 0 && x % g == 0 && y % g == 0
{
    if y == 0 {
        // Base case: gcd(x, 0) = x
    } else {
        GcdDivides(y, x % y);
    }
}

lemma GcdMaximal(x: int, y: int, d: int)
    requires x >= 0 && y >= 0
    requires x > 0 || y > 0
    requires d > 0 && x % d == 0 && y % d == 0
    ensures d <= gcd(x, y)
{
    if y == 0 {
        // Base case: gcd(x, 0) = x
    } else {
        GcdMaximal(y, x % y, d);
    }
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
{
    /* code modified by LLM (iteration 5): simplified implementation using standard Euclidean algorithm */
    if a == 0 && b == 0 {
        result := 1;
        return;
    }
    
    var x := if a < 0 then -a else a;
    var y := if b < 0 then -b else b;
    
    while y != 0
        invariant x >= 0 && y >= 0
        invariant x > 0 || y > 0
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    
    result := x;
    
    var abs_a := if a < 0 then -a else a;
    var abs_b := if b < 0 then -b else b;
    
    if abs_a > 0 || abs_b > 0 {
        GcdDivides(abs_a, abs_b);
        forall d | d > 0 && a % d == 0 && b % d == 0
            ensures d <= result
        {
            GcdMaximal(abs_a, abs_b, d);
        }
    }
}
// </vc-code>
