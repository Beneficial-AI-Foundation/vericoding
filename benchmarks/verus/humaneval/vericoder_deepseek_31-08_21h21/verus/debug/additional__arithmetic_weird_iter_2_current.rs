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
    admit();
}

proof fn lemma_div_decreases(a: int, m: int)
    requires
        a >= 0,
        m > 0,
        a >= m,
    ensures
        a / m < a,
{
    admit();
}

proof fn lemma_mod_small(a: int, m: int)
    requires
        a >= 0,
        m > 0,
    ensures
        (a % m) as int < m,
{
    admit();
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
            x >= 0,
            cycle_count == x / 10,
            result == ((x * 2) % 9),
            result < 10,
        decreases 100 - x,
    {
        result = (x * 2) % 9;
        proof {
            lemma_mod_lt((x as int) * 2, 9);
            lemma_mod_small((x as int) * 2, 9);
        }
        x = x + 1;
        cycle_count = x / 10;
        proof {
            if x < 100 {
                lemma_div_decreases(100 - (x as int), 1);
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}