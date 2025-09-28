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
/* helper modified by LLM (iteration 5): added decreases clause to fix compilation error */
proof fn lemma_xor_range_base(a: int)
    requires 0 <= a
    ensures xor_range(a, a) == a
{
}

proof fn lemma_xor_range_step(a: int, b: int)
    requires 0 <= a < b
    ensures xor_range(a, b) == xor_int(a, xor_range(a + 1, b))
{
}

proof fn lemma_xor_int_bounds(x: int, y: int)
    requires x >= 0, y >= 0
    ensures xor_int(x, y) >= 0
    decreases x + y
{
    if x == 0 && y == 0 {
    } else if x == 0 {
    } else if y == 0 {
    } else {
        lemma_xor_int_bounds(x / 2, y / 2);
    }
}

proof fn lemma_xor_range_bounds(a: int, b: int)
    requires 0 <= a <= b
    ensures xor_range(a, b) >= 0
    decreases b - a
{
    if a == b {
        lemma_xor_range_base(a);
    } else {
        lemma_xor_range_bounds(a + 1, b);
        lemma_xor_int_bounds(a, xor_range(a + 1, b));
        lemma_xor_range_step(a, b);
    }
}

proof fn lemma_xor_result_in_bounds(x: i32, y: i32)
    requires x >= 0, y >= 0, x <= 0x7fffffff, y <= 0x7fffffff
    ensures (x as u32) ^ (y as u32) <= 0x7fffffff
{
    assert((x as u32) <= 0x7fffffff);
    assert((y as u32) <= 0x7fffffff);
    assert((x as u32) ^ (y as u32) <= 0x7fffffff);
}

proof fn lemma_current_increment_safe(current: i32, b: i32)
    requires current <= b, current >= 0, b <= 0x7fffffff
    ensures current + 1 <= 0x7fffffff
{
    assert(current <= b);
    assert(b <= 0x7fffffff);
    assert(current + 1 <= b + 1);
    assert(b + 1 <= 0x7fffffff + 1);
}

proof fn lemma_xor_range_extend(a: int, current: int)
    requires 0 <= a < current
    ensures xor_range(a, current) == xor_int(xor_range(a, current - 1), current)
    decreases current - a
{
    if current == a + 1 {
        lemma_xor_range_base(a);
        lemma_xor_range_step(a, current);
    } else {
        lemma_xor_range_extend(a, current - 1);
        lemma_xor_range_step(a, current);
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
    /* code modified by LLM (iteration 5): fixed loop invariant and xor range construction */
    if a == b {
        proof {
            lemma_xor_range_base(a as int);
        }
        return a;
    }
    
    let mut current = a + 1;
    let mut result = a;
    
    while current <= b
        invariant
            a < current <= b + 1,
            result >= 0,
            current >= 0,
            current <= 0x7fffffff + 1,
            result <= 0x7fffffff,
            result as int == xor_range(a as int, (current - 1) as int),
        decreases b - current
    {
        proof {
            lemma_xor_int_bounds(result as int, current as int);
            lemma_xor_result_in_bounds(result, current);
            lemma_current_increment_safe(current, b);
            lemma_xor_range_extend(a as int, current as int);
        }
        
        let new_result = (result as u32) ^ (current as u32);
        result = new_result as i32;
        current = current + 1;
    }
    
    proof {
        lemma_xor_range_bounds(a as int, b as int);
    }
    
    result
}
// </vc-code>

}

fn main() {}