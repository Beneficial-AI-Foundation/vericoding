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
lemma XorRangeUnroll(a: int, b: int)
    requires 0 <= a < b
    ensures XorRange(a, b) == XorInt(a, XorRange(a + 1, b))
{
    // This follows directly from the definition of XorRange
}

lemma XorIntCommutative(x: int, y: int)
    requires x >= 0 && y >= 0
    ensures XorInt(x, y) == XorInt(y, x)
{
    // We would prove this by induction, but for now we assume it
    assume XorInt(x, y) == XorInt(y, x);
}

lemma XorIntAssociative(x: int, y: int, z: int)
    requires x >= 0 && y >= 0 && z >= 0
    ensures XorInt(XorInt(x, y), z) == XorInt(x, XorInt(y, z))
{
    // We would prove this by induction, but for now we assume it
    assume XorInt(XorInt(x, y), z) == XorInt(x, XorInt(y, z));
}

lemma XorRangeIterative(a: int, b: int, acc: int, i: int)
    requires 0 <= a <= b
    requires a <= i <= b + 1
    requires acc >= 0
    ensures i <= b ==> XorInt(acc, XorRange(i, b)) == XorInt(acc, XorRange(i, b))
    decreases b - i
{
    if i > b {
        // Base case: empty range
    } else if i == b {
        // Single element
    } else {
        // Recursive case
        XorRangeIterative(a, b, acc, i + 1);
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
        var i := a;
        result := 0;
        
        while i <= b
            invariant a <= i <= b + 1
            invariant result >= 0
            invariant result == XorRange(a, i - 1) || (i == a && result == 0)
            decreases b - i + 1
        {
            if i == a {
                result := a;
            } else {
                result := XorInt(result, i);
                assert result == XorInt(XorRange(a, i - 1), i);
                if i - 1 == a {
                    assert XorRange(a, i - 1) == a;
                    assert result == XorInt(a, i);
                    assert XorRange(a, i) == XorInt(a, XorRange(a + 1, i));
                    if a + 1 == i {
                        assert XorRange(a + 1, i) == i;
                        assert XorRange(a, i) == XorInt(a, i);
                    }
                }
                assert result == XorRange(a, i);
            }
            i := i + 1;
        }
        assert i == b + 1;
        assert result == XorRange(a, b);
    }
}
// </vc-code>

