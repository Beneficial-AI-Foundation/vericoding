// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(a: int, b: int) -> bool {
        0 <= a <= b
    }
    
    spec fn xor_int(x: int, y: int) -> int
        decreases x + y
    {
        if x >= 0 && y >= 0 {
            if x == 0 && y == 0 { 0 }
            else if x == 0 { y }
            else if y == 0 { x }
            else {
                let bit_x = x % 2;
                let bit_y = y % 2;
                let xor_bit: int = if bit_x != bit_y { 1 } else { 0 };
                xor_bit + 2 * xor_int(x / 2, y / 2)
            }
        } else {
            0
        }
    }
    
    spec fn xor_range(a: int, b: int) -> int
        decreases b - a
    {
        if 0 <= a <= b {
            if a == b { a }
            else { xor_int(a, xor_range(a + 1, b)) }
        } else {
            0
        }
    }
// </vc-preamble>

// <vc-helpers>
fn compute_xor(x: i32, y: i32) -> (res: i32)
    requires
        x >= 0,
        y >= 0,
    ensures
        res >= 0,
        res as int == xor_int(x as int, y as int),
    decreases x + y
{
    if x == 0 {
        y
    } else if y == 0 {
        x
    } else {
        let bit_x = x % 2;
        let bit_y = y % 2;
        let xor_bit: i32 = if bit_x != bit_y { 1 } else { 0 };
        let rest = compute_xor(x / 2, y / 2);
        xor_bit + 2 * rest
    }
}

proof fn lemma_xor_int_identity(x: int)
    requires x >= 0,
    ensures xor_int(x, 0) == x,
    decreases x
{
    if x > 0 {
        lemma_xor_int_identity(x / 2);
    }
}

proof fn lemma_xor_int_commutative(x: int, y: int)
    requires x >= 0, y >= 0,
    ensures xor_int(x, y) == xor_int(y, x),
    decreases x + y
{
    if x > 0 || y > 0 {
        lemma_xor_int_commutative(x / 2, y / 2);
    }
}

proof fn lemma_xor_int_associative(x: int, y: int, z: int)
    requires x >= 0, y >= 0, z >= 0,
    ensures xor_int(xor_int(x, y), z) == xor_int(x, xor_int(y, z)),
    decreases x + y + z
{
    if x > 0 || y > 0 || z > 0 {
        lemma_xor_int_associative(x / 2, y / 2, z / 2);
    }
}

proof fn lemma_xor_range_accumulate(a: int, i: int)
    requires 0 <= a <= i,
    ensures xor_range(a, i) == xor_int(xor_range(a, i - 1), i),
    decreases i - a
{
    if a == i {
        lemma_xor_int_identity(i);
        lemma_xor_int_commutative(0, i);
    } else {
        lemma_xor_range_accumulate(a + 1, i);
        lemma_xor_int_associative(a, xor_range(a + 1, i - 1), i);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i32, b: i32) -> (result: i32)
    requires 
        a >= 0,
        b >= 0,
        a <= b
    ensures 
        result >= 0,
        result as int == xor_range(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    let mut i = a;
    let mut result: i32 = 0;
    while i <= b
        invariant
            a <= i <= b + 1,
            result as int == xor_range(a as int, (i - 1) as int),
        decreases b - i
    {
        proof {
            lemma_xor_range_accumulate(a as int, i as int);
        }
        result = compute_xor(result, i);
        i = i + 1;
    }
    result
}
// </vc-code>

}

fn main() {}