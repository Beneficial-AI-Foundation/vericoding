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
lemma XorRangeIterativeCorrectness(a: int, b: int)
    requires 0 <= a <= b
    ensures XorRange(a, b) >= 0
    decreases b - a
{
    if a == b {
        assert XorRange(a, b) == a;
        assert a >= 0;
    } else {
        XorRangeIterativeCorrectness(a + 1, b);
        assert XorRange(a + 1, b) >= 0;
        assert XorInt(a, XorRange(a + 1, b)) >= 0;
    }
}

lemma XorRangeUnroll(a: int, b: int)
    requires 0 <= a < b
    ensures XorRange(a, b) == XorInt(a, XorRange(a + 1, b))
{
    // Direct from definition
}

lemma XorRangeExtend(a: int, k: int)
    requires 0 <= a <= k
    ensures XorRange(a, k + 1) == XorInt(XorRange(a, k), k + 1)
    decreases k - a
{
    if a == k {
        assert XorRange(a, k) == a;
        assert XorRange(a, k + 1) == XorInt(a, k + 1);
        assert XorInt(XorRange(a, k), k + 1) == XorInt(a, k + 1);
    } else {
        assert XorRange(a, k) == XorInt(a, XorRange(a + 1, k));
        assert XorRange(a, k + 1) == XorInt(a, XorRange(a + 1, k + 1));
        XorRangeExtend(a + 1, k);
        assert XorRange(a + 1, k + 1) == XorInt(XorRange(a + 1, k), k + 1);
        
        calc {
            XorInt(XorRange(a, k), k + 1);
            XorInt(XorInt(a, XorRange(a + 1, k)), k + 1);
            XorInt(a, XorInt(XorRange(a + 1, k), k + 1));
            { assert XorRange(a + 1, k + 1) == XorInt(XorRange(a + 1, k), k + 1); }
            XorInt(a, XorRange(a + 1, k + 1));
            XorRange(a, k + 1);
        }
    }
}

lemma XorIntCommutative(x: int, y: int)
    requires x >= 0 && y >= 0
    ensures XorInt(x, y) == XorInt(y, x)
    decreases x + y
{
    if x == 0 && y == 0 {
        assert XorInt(x, y) == 0 == XorInt(y, x);
    } else if x == 0 {
        assert XorInt(x, y) == y == XorInt(y, x);
    } else if y == 0 {
        assert XorInt(x, y) == x == XorInt(y, x);
    } else {
        var bit_x := x % 2;
        var bit_y := y % 2;
        var xor_bit := if bit_x != bit_y then 1 else 0;
        XorIntCommutative(x / 2, y / 2);
        assert XorInt(x / 2, y / 2) == XorInt(y / 2, x / 2);
        assert bit_x != bit_y == bit_y != bit_x;
        
        calc {
            XorInt(x, y);
            xor_bit + 2 * XorInt(x / 2, y / 2);
            xor_bit + 2 * XorInt(y / 2, x / 2);
            XorInt(y, x);
        }
    }
}

lemma XorIntAssociative(x: int, y: int, z: int)
    requires x >= 0 && y >= 0 && z >= 0
    ensures XorInt(XorInt(x, y), z) == XorInt(x, XorInt(y, z))
    decreases x + y + z
{
    if x == 0 && y == 0 && z == 0 {
        assert XorInt(XorInt(x, y), z) == 0 == XorInt(x, XorInt(y, z));
    } else if x == 0 && y == 0 {
        assert XorInt(XorInt(x, y), z) == z == XorInt(x, XorInt(y, z));
    } else if x == 0 && z == 0 {
        assert XorInt(XorInt(x, y), z) == y == XorInt(x, XorInt(y, z));
    } else if y == 0 && z == 0 {
        assert XorInt(XorInt(x, y), z) == x == XorInt(x, XorInt(y, z));
    } else if x == 0 {
        assert XorInt(XorInt(x, y), z) == XorInt(y, z) == XorInt(x, XorInt(y, z));
    } else if y == 0 {
        assert XorInt(XorInt(x, y), z) == XorInt(x, z) == XorInt(x, XorInt(y, z));
    } else if z == 0 {
        assert XorInt(XorInt(x, y), z) == XorInt(x, y) == XorInt(x, XorInt(y, z));
    } else {
        var bit_x := x % 2;
        var bit_y := y % 2;
        var bit_z := z % 2;
        XorIntAssociative(x / 2, y / 2, z / 2);
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
    if a == b {
        result := a;
    } else {
        var current := a;
        result := current;
        current := current + 1;
        
        while current <= b
            invariant a < current <= b + 1
            invariant result == XorRange(a, current - 1)
            invariant result >= 0
            decreases b - current + 1
        {
            XorRangeExtend(a, current - 1);
            result := XorInt(result, current);
            current := current + 1;
        }
    }
}
// </vc-code>

