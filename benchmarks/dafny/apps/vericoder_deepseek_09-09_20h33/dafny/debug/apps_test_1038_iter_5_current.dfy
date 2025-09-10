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
        assert XorRange(a + 1, b) == XorInt(XorRange(a + 1, c), XorRange(c + 1, b));
        XorIntAssociative(a, XorRange(a + 1, c), XorRange(c + 1, b));
        assert XorInt(a, XorInt(XorRange(a + 1, c), XorRange(c + 1, b))) == XorInt(XorInt(a, XorRange(a + 1, c)), XorRange(c + 1, b));
        assert XorInt(XorInt(a, XorRange(a + 1, c)), XorRange(c + 1, b)) == XorInt(XorRange(a, c), XorRange(c + 1, b));
    } else if c < b {
        XorRangeSplit(a, b, c + 1);
    } else {
        assert c == b;
        assert XorRange(a, b) == a;
        assert XorRange(a, c) == XorRange(a, b) == a;
        XorRangeSingle(b);
        assert XorRange(b + 1, b) == 0;
        assert XorInt(a, 0) == a;
    }
}

lemma XorRangeEmpty(x: int)
    requires x >= 0
    ensures XorRange(x + 1, x) == 0
{
    // This is vacuously true by the precondition of XorRange
}

lemma XorRangeSingle(x: int)
    requires x >= 0
    ensures XorRange(x, x) == x
{
}

lemma XorIntAssociative(x: int, y: int, z: int)
    requires x >= 0 && y >= 0 && z >= 0
    ensures XorInt(XorInt(x, y), z) == XorInt(x, XorInt(y, z))
    decreases x + y + z
{
    if x == 0 {
        // Base case: x = 0
        assert XorInt(XorInt(0, y), z) == XorInt(y, z);
        assert XorInt(0, XorInt(y, z)) == XorInt(y, z);
    } else if y == 0 {
        // Base case: y = 0
        assert XorInt(XorInt(x, 0), z) == XorInt(x, z);
        assert XorInt(x, XorInt(0, z)) == XorInt(x, z);
    } else if z == 0 {
        // Base case: z = 0
        assert XorInt(XorInt(x, y), 0) == XorInt(x, y);
        assert XorInt(x, XorInt(y, 0)) == XorInt(x, y);
    } else {
        // Recursive case for all positive
        var x2 := x / 2;
        var y2 := y / 2;
        var z2 := z / 2;
        var bit_x := x % 2;
        var bit_y := y % 2;
        var bit_z := z % 2;
        
        XorIntAssociative(x2, y2, z2);
        
        // Check bit-level associativity
        var left_bit := if (bit_x != bit_y) != bit_z then 1 else 0;
        var right_bit := if bit_x != (bit_y != bit_z) then 1 else 0;
        assert left_bit == right_bit;
    }
}

lemma XorIntZero(x: int)
    requires x >= 0
    ensures XorInt(x, 0) == x
{
    if x == 0 {
    } else {
        XorIntZero(x / 2);
    }
}

lemma XorIntSame(x: int)
    requires x >= 0
    ensures XorInt(x, x) == 0
{
    if x == 0 {
    } else {
        XorIntSame(x / 2);
    }
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
    result := a;
    var current := a + 1;
    
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

