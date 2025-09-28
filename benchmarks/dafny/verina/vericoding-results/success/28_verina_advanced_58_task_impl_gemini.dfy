// <vc-preamble>
predicate NthUglyNumberPrecond(n: nat)
{
    n > 0
}
// </vc-preamble>

// <vc-helpers>
function Min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method NthUglyNumber(n: int) returns (result: int)
    requires n > 0
    ensures result > 0
// </vc-spec>
// <vc-code>
{
    var ugly := new int[n];
    ugly[0] := 1;

    var i2: nat := 0;
    var i3: nat := 0;
    var i5: nat := 0;

    var i: nat := 1;
    while i < n
        invariant 1 <= i <= n
        invariant ugly[0] == 1
        invariant forall k :: 0 <= k < i ==> ugly[k] >= 1
        invariant 0 <= i2 < i
        invariant 0 <= i3 < i
        invariant 0 <= i5 < i
    {
        var next2 := ugly[i2] * 2;
        var next3 := ugly[i3] * 3;
        var next5 := ugly[i5] * 5;

        var next_ugly := Min(next2, Min(next3, next5));
        ugly[i] := next_ugly;

        if next_ugly == next2 {
            i2 := i2 + 1;
        }
        if next_ugly == next3 {
            i3 := i3 + 1;
        }
        if next_ugly == next5 {
            i5 := i5 + 1;
        }
        i := i + 1;
    }

    result := ugly[n-1];
}
// </vc-code>
