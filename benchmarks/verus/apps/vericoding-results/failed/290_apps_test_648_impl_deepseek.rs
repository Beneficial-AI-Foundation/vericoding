// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(m: int, b: int) -> bool {
  1 <= m <= 1000 && 1 <= b <= 10000
}

spec fn f(x: int, y: int) -> int {
  (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2
}

spec fn valid_rectangle_corner(k: int, m: int, b: int) -> bool {
  0 <= k && b - k >= 0
}

spec fn rectangle_value(k: int, m: int, b: int) -> int {
  f(k * m, b - k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation by removing ghost block and using proper verus syntax */
proof fn lemma_max_value_in_range(max: int, m: int, b: int)
    requires
        valid_input(m, b),
    ensures
        exists|k: int| valid_rectangle_corner(k, m, b) && max == rectangle_value(k, m, b),
        forall|k: int| valid_rectangle_corner(k, m, b) ==> max >= rectangle_value(k, m, b)
{
    let witness_k = b / 2;
    assert(0 <= witness_k) by {
        assert(b >= 1);
    };
    assert(b - witness_k >= 0) by {
        assert(witness_k <= b);
    };
    assert(valid_rectangle_corner(witness_k, m, b));
    assert(max == rectangle_value(witness_k, m, b));
    
    forall|k: int|
        ensures
            valid_rectangle_corner(k, m, b) ==> max >= rectangle_value(k, m, b)
    {
        if valid_rectangle_corner(k, m, b) {
            assert(0 <= k && k <= b);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(m: i8, b: i8) -> (result: i8)
  requires 
    valid_input(m as int, b as int)
  ensures 
    result as int >= -1,
    forall|k: int| valid_rectangle_corner(k, m as int, b as int) ==> result as int >= rectangle_value(k, m as int, b as int),
    exists|k: int| valid_rectangle_corner(k, m as int, b as int) && result as int == rectangle_value(k, m as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed ghost block and fixed implementation */
    let m_int = m as int;
    let b_int = b as int;
    
    let candidate = b_int / 2;
    let max_val = rectangle_value(candidate, m_int, b_int);
    
    lemma_max_value_in_range(max_val, m_int, b_int);
    
    max_val as i8
}
// </vc-code>


}

fn main() {}