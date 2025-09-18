// <vc-preamble>
predicate NthUglyNumberPrecond(n: nat)
{
    n > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes, seems correct */
function min3(a: int, b: int, c: int): int {
    if a <= b && a <= c then a
    else if b <= a && b <= c then b
    else c
}
// </vc-helpers>

// <vc-spec>
method NthUglyNumber(n: int) returns (result: int)
    requires n > 0
    ensures result > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected array initialization syntax. */
{
    var uglyNumbers: array<int>;
    uglyNumbers := new int[n];
    uglyNumbers[0] := 1;
    var i2 := 0;
    var i3 := 0;
    var i5 := 0;
    var nextMultipleOf2 := 2;
    var nextMultipleOf3 := 3;
    var nextMultipleOf5 := 5;

    var i := 1;
    while i < n
        invariant 0 <= i <= n
        invariant uglyNumbers[0] == 1
        invariant forall k :: 0 <= k < i ==> uglyNumbers[k] > 0
        invariant 0 <= i2 < i || i2 == 0
        invariant 0 <= i3 < i || i3 == 0
        invariant 0 <= i5 < i || i5 == 0
        invariant (i2 < i ==> nextMultipleOf2 == uglyNumbers[i2] * 2) // Guarded for initial state
        invariant (i3 < i ==> nextMultipleOf3 == uglyNumbers[i3] * 3) // Guarded for initial state
        invariant (i5 < i ==> nextMultipleOf5 == uglyNumbers[i5] * 5) // Guarded for initial state
        invariant forall k :: 0 <= k < i ==> uglyNumbers[k] == uglyNumbers[k]
    {
        var nextUgly := min3(nextMultipleOf2, nextMultipleOf3, nextMultipleOf5);
        uglyNumbers[i] := nextUgly;

        if nextUgly == nextMultipleOf2 {
            i2 := i2 + 1;
            // uglyNumbers[i2] must be within bounds. This relies on previous fills.
            nextMultipleOf2 := uglyNumbers[i2] * 2;
        }
        if nextUgly == nextMultipleOf3 {
            i3 := i3 + 1;
            // uglyNumbers[i3] must be within bounds.
            nextMultipleOf3 := uglyNumbers[i3] * 3;
        }
        if nextUgly == nextMultipleOf5 {
            i5 := i5 + 1;
            // uglyNumbers[i5] must be within bounds.
            nextMultipleOf5 := uglyNumbers[i5] * 5;
        }
        i := i + 1;
    }
    result := uglyNumbers[n - 1];
}
// </vc-code>
