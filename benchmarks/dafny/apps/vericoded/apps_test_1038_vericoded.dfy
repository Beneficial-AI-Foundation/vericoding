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
lemma XorRangeUnfold(a: int, b: int)
    requires 0 <= a < b
    ensures XorRange(a, b) == XorInt(a, XorRange(a + 1, b))
{
    // This follows directly from the definition of XorRange
}

lemma XorRangeStep(a: int, b: int)
    requires 0 <= a <= b
    ensures XorRange(a, b) == if a == b then a else XorInt(XorRange(a, b - 1), b)
    decreases b - a
{
    if a == b {
        // Base case: XorRange(a, a) == a by definition
    } else if a == b - 1 {
        // XorRange(a, a + 1) == XorInt(a, XorRange(a + 1, a + 1)) == XorInt(a, a + 1)
        assert XorRange(a, b) == XorInt(a, XorRange(a + 1, b));
        assert XorRange(a + 1, b) == b;
        assert XorRange(a, b) == XorInt(a, b);
        assert XorRange(a, b - 1) == a;
        assert XorInt(XorRange(a, b - 1), b) == XorInt(a, b);
    } else {
        // For a < b - 1
        XorRangeUnfold(a, b);
        assert XorRange(a, b) == XorInt(a, XorRange(a + 1, b));
        
        XorRangeStep(a + 1, b);
        assert XorRange(a + 1, b) == XorInt(XorRange(a + 1, b - 1), b);
        
        assert XorRange(a, b) == XorInt(a, XorInt(XorRange(a + 1, b - 1), b));
        
        // We need associativity here
        XorAssociative(a, XorRange(a + 1, b - 1), b);
        assert XorInt(a, XorInt(XorRange(a + 1, b - 1), b)) == XorInt(XorInt(a, XorRange(a + 1, b - 1)), b);
        
        XorRangeUnfold(a, b - 1);
        assert XorRange(a, b - 1) == XorInt(a, XorRange(a + 1, b - 1));
        
        assert XorRange(a, b) == XorInt(XorRange(a, b - 1), b);
    }
}

lemma XorAssociative(x: int, y: int, z: int)
    requires x >= 0 && y >= 0 && z >= 0
    ensures XorInt(XorInt(x, y), z) == XorInt(x, XorInt(y, z))
    decreases x + y + z
{
    if x == 0 {
        assert XorInt(0, y) == y;
        assert XorInt(XorInt(0, y), z) == XorInt(y, z);
        assert XorInt(0, XorInt(y, z)) == XorInt(y, z);
    } else if y == 0 {
        assert XorInt(x, 0) == x;
        assert XorInt(XorInt(x, 0), z) == XorInt(x, z);
        assert XorInt(x, XorInt(0, z)) == XorInt(x, z);
    } else if z == 0 {
        assert XorInt(XorInt(x, y), 0) == XorInt(x, y);
        assert XorInt(y, 0) == y;
        assert XorInt(x, XorInt(y, 0)) == XorInt(x, y);
    } else {
        var bit_x := x % 2;
        var bit_y := y % 2;
        var bit_z := z % 2;
        
        var xy_bit := if bit_x != bit_y then 1 else 0;
        var yz_bit := if bit_y != bit_z then 1 else 0;
        
        var xy_z_bit := if xy_bit != bit_z then 1 else 0;
        var x_yz_bit := if bit_x != yz_bit then 1 else 0;
        
        // XOR is associative at bit level
        assert xy_z_bit == x_yz_bit;
        
        XorAssociative(x / 2, y / 2, z / 2);
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
        var i := a + 1;
        result := a;
        
        while i <= b
            invariant a < i <= b + 1
            invariant result >= 0
            invariant result == XorRange(a, i - 1)
        {
            XorRangeStep(a, i);
            assert XorRange(a, i) == XorInt(XorRange(a, i - 1), i);
            
            result := XorInt(result, i);
            
            i := i + 1;
        }
    }
}
// </vc-code>

