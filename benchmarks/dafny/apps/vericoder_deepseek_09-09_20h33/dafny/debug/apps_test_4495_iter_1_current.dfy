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
lemma CountDivisibleInRangeLemma(a: int, b: int, x: int)
    requires ValidInput(a, b, x)
    ensures CountDivisibleInRange(a, b, x) == (b / x) - ((a - 1) / x)
{
    // This lemma establishes the relationship between the two cases
}

lemma DivModProperties(a: int, x: int)
    requires x > 0
    ensures a % x >= 0 && a % x < x
    ensures a == x * (a / x) + (a % x)
{
    // Fundamental properties of division and modulus
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
    var low := a;
    var high := b;
    
    // Calculate number of multiples using integer division
    var first_multiple := if low % x == 0 then low else low + (x - low % x);
    var last_multiple := high - (high % x);
    
    if first_multiple > last_multiple {
        count := 0;
    } else {
        count := (last_multiple - first_multiple) / x + 1;
    }
}
// </vc-code>

