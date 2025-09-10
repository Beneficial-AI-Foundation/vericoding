predicate ValidInput(a: int, b: int, x: int)
{
    a >= 0 && b >= a && x > 0
}

function CountDivisibleInRange(a: int, b: int, x: int): int
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a, b, x) >= 0
{
    if a == 0 then
        b / x + 1
    else
        b / x - (a - 1) / x
}

// <vc-helpers>
lemma CountDivisibleInRange_properties(a: int, b: int, x: int)
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a,b,x) == (b / x) - ((a-1) / x)
    ensures (a-1) >= 0 ==> (a-1)/x <= (b)/x
{
    if a == 0 {
      calc {
        b / x + 1;
        (b / x) - (-1) / x;
      }
    } else {
        // (a-1)/x <= b/x is true by simple arithmetic
    }
}
// </vc-helpers>

// <vc-spec>
method CountDivisible(a: int, b: int, x: int) returns (count: int)
    requires ValidInput(a, b, x)
    ensures count == CountDivisibleInRange(a, b, x)
    ensures count >= 0
// </vc-spec>
// <vc-code>
{
    // The proof that CountDivisibleInRange_properties holds is necessary for the postcondition verification.
    // However, the `ensures` clause of the method `CountDivisible` already includes `count == CountDivisibleInRange(a, b, x)`.
    // The implementation directly calls `CountDivisibleInRange` function, whose properties are assumed to hold.
    // The `CountDivisibleInRange_properties` lemma is more for demonstrating internal properties of CountDivisibleInRange
    // relevant for manual reasoning, not strictly needed for this particular method body implementation via direct call.
    // The verifier usually handles properties of pure functions quite well.

    CountDivisibleInRange_properties(a, b, x); // This lemma call helps the verifier understand the properties

    if a == 0 {
        count := b / x + 1;
    } else {
        count := b / x - (a - 1) / x;
    }
}
// </vc-code>

