// <vc-preamble>
predicate NthUglyNumberPrecond(n: nat)
{
    n > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simplified to focus on basic operations needed for ugly number generation */
function Min3(a: int, b: int, c: int): int
{
    if a <= b && a <= c then a
    else if b <= c then b
    else c
}

lemma Min3Positive(a: int, b: int, c: int)
    requires a > 0 && b > 0 && c > 0
    ensures Min3(a, b, c) > 0
{
}
// </vc-helpers>

// <vc-spec>
method NthUglyNumber(n: int) returns (result: int)
    requires n > 0
    ensures result > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added invariants to prove result > 0 */
    var ugly := new int[n];
    ugly[0] := 1;
    var i2, i3, i5 := 0, 0, 0;
    var next2, next3, next5 := 2, 3, 5;
    
    var i := 1;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= i2 < i
        invariant 0 <= i3 < i
        invariant 0 <= i5 < i
        invariant forall j :: 0 <= j < i ==> ugly[j] > 0
        invariant next2 > 0 && next3 > 0 && next5 > 0
    {
        var nextUgly := Min3(next2, next3, next5);
        Min3Positive(next2, next3, next5);
        ugly[i] := nextUgly;
        
        if nextUgly == next2 {
            i2 := i2 + 1;
            next2 := 2 * ugly[i2];
        }
        if nextUgly == next3 {
            i3 := i3 + 1;
            next3 := 3 * ugly[i3];
        }
        if nextUgly == next5 {
            i5 := i5 + 1;
            next5 := 5 * ugly[i5];
        }
        
        i := i + 1;
    }
    
    result := ugly[n - 1];
}
// </vc-code>
