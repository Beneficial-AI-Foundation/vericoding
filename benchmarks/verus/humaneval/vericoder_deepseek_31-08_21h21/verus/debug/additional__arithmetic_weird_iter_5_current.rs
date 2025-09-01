use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mod_lt(a: int, m: int)
    requires
        a >= 0,
        m > 0,
    ensures
        a % m >= 0,
        a % m < m,
{
    assert(0 <= a % m < m);
}

proof fn lemma_div_decreases(a: int, m: int)
    requires
        a >= 0,
        m > 0,
        a >= m,
    ensures
        a / m < a,
{
    if a > 0 {
        assert(a / m <= a / 1);
        assert(a / m <= a);
    }
}

proof fn lemma_mod_small(a: int, m: int)
    requires
        a >= 0,
        m > 0,
    ensures
        (a % m) as int < m,
{
    lemma_mod_lt(a, m);
}

proof fn lemma_x_plus_one_div_ten(x: int)
    requires
        x >= 0,
    ensures
        (x + 1) / 10 == x / 10 + (if (x + 1) % 10 == 0 { 1 } else { 0 }),
{
    if (x + 1) % 10 == 0 {
        assert((x + 1) / 10 == x / 10 + 1);
    } else {
        assert((x + 1) / 10 == x / 10);
    }
}

proof fn lemma_result_lt_nine(x: int)
    requires
        x >= 0,
    ensures
        (x * 2) % 9 < 9,
{
    lemma_mod_lt(x * 2, 9);
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    // post-conditions-start
    ensures
        result < 10
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: i32 = 0;
    let mut x: i32 = 0;
    let mut cycle_count = 0;
    
    while x < 100
        invariant
            0 <= x <= 100,
            cycle_count == x / 10,
            result == ((x * 2) % 9) as i32,
            result >= 0,
            result < 9,
        decreases 100 - x,
    {
        result = (x * 2) % 9;
        proof {
            lemma_result_lt_nine(x as int);
        }
        x = x + 1;
        proof {
            lemma_x_plus_one_div_ten((x - 1) as int);
        }
        cycle_count = x / 10;
    }
    
    result
}
// </vc-code>

fn main() {}
}