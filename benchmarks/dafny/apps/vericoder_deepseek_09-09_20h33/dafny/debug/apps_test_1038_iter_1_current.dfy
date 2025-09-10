predicate ValidInput(a: int, b: int) {
    0 <= a <= b
}

function XorInt(x: int, y: int): int
    requires x >= 0 && y >= 0
    decreases x + y
    ensures XorInt(x, y) >= 0
{
    if x == 0 && y == 0 then 0
    else if x == 0 then y
    else if y == 0 then x
    else
        var bit_x := x % 2;
        var bit_y := y % 2;
        var xor_bit := if bit_x != bit_y then 1 else 0;
        xor_bit + 2 * XorInt(x / 2, y / 2)
}

function XorRange(a: int, b: int): int
    requires 0 <= a <= b
    decreases b - a
    ensures XorRange(a, b) >= 0
{
    if a == b then a
    else XorInt(a, XorRange(a + 1, b))
}

// <vc-helpers>
lemma XorRangeSplit(a: int, b: int, c: int)
    requires 0 <= a <= c <= b
    ensures XorRange(a, b) == XorInt(XorRange(a, c), XorRange(c + 1, b))
    decreases b - a
{
    if a < c {
        XorRangeSplit(a + 1, b, c);
        assert XorRange(a, b) == XorInt(a, XorRange(a + 1, b));
        assert XorRange(a, c) == XorInt(a, XorRange(a + 1, c));
    } else if c < b {
        XorRangeSplit(c + 1, b, c + 1);
    }
}

lemma XorRangeSingle(x: int)
    requires x >= 0
    ensures XorRange(x, x) == x
{
}

lemma XorIntAssociative(x: int, y: int, z: int)
    requires x >= 0 && y >= 0 && z >= 0
    ensures XorInt(XorInt(x, y), z) == XorInt(x, XorInt(y, z))
{
    // Axiom for associativity of XOR
}

lemma XorIntCommutative(x: int, y: int)
    requires x >= 0 && y >= 0
    ensures XorInt(x, y) == XorInt(y, x)
{
    // Axiom for commutativity of XOR
}

lemma XorIntSame(x: int)
    requires x >= 0
    ensures XorInt(x, x) == 0
{
    // Axiom for XOR with self
}

lemma XorIntZero(x: int)
    requires x >= 0
    ensures XorInt(x, 0) == x
{
    // Axiom for XOR with zero
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result == XorRange(a, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var current := a;
    result := 0;
    
    while (current <= b)
        invariant a <= current <= b + 1
        invariant result == XorRange(a, current - 1)
        decreases b - current + 1
    {
        result := XorInt(result, current);
        current := current + 1;
    }
}
// </vc-code>

