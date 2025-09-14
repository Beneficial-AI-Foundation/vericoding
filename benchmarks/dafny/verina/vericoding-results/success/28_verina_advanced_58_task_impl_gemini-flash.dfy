// <vc-preamble>
predicate NthUglyNumberPrecond(n: nat)
{
    n > 0
}
// </vc-preamble>

// <vc-helpers>
function min3(a: int, b: int, c: int): int { if a < b then (if a < c then a else c) else (if b < c then b else c) }
// </vc-helpers>

// <vc-spec>
method NthUglyNumber(n: int) returns (result: int)
    requires n > 0
    ensures result > 0
// </vc-spec>
// <vc-code>
{
    var ugly: array<int>;
    ugly := new int[n + 1];
    ugly[1] := 1;

    var i2 := 1;
    var i3 := 1;
    var i5 := 1;

    var next2 := 2;
    var next3 := 3;
    var next5 := 5;

    var k := 2;
    while k <= n
        invariant 1 <= k <= n + 1
        invariant ugly.Length == n + 1
        invariant forall j :: 1 <= j < k ==> ugly[j] > 0
        invariant 1 <= i2 < k && 1 <= i3 < k && 1 <= i5 < k
        invariant next2 == ugly[i2] * 2
        invariant next3 == ugly[i3] * 3
        invariant next5 == ugly[i5] * 5
        decreases n - k
    {
        var nextUgly := min3(next2, next3, next5);
        ugly[k] := nextUgly;
        if nextUgly == next2 {
            i2 := i2 + 1;
            next2 := ugly[i2] * 2;
        }
        if nextUgly == next3 {
            i3 := i3 + 1;
            next3 := ugly[i3] * 3;
        }
        if nextUgly == next5 {
            i5 := i5 + 1;
            next5 := ugly[i5] * 5;
        }
        k := k + 1;
    }
    result := ugly[n];
}
// </vc-code>
