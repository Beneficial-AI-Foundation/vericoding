// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a1: int, a2: int, a3: int) -> bool {
    1 <= a1 <= 100 && 1 <= a2 <= 100 && 1 <= a3 <= 100
}

spec fn max_of_three(a1: int, a2: int, a3: int) -> int {
    if a1 >= a2 && a1 >= a3 { a1 } else if a2 >= a3 { a2 } else { a3 }
}

spec fn min_of_three(a1: int, a2: int, a3: int) -> int {
    if a1 <= a2 && a1 <= a3 { a1 } else if a2 <= a3 { a2 } else { a3 }
}

spec fn minimum_cost(a1: int, a2: int, a3: int) -> int {
    max_of_three(a1, a2, a3) - min_of_three(a1, a2, a3)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial helper to avoid external lemmas */
fn triv_helper()
    ensures
        true,
{
    proof {
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a1: i8, a2: i8, a3: i8) -> (result: i8)
    requires 
        valid_input(a1 as int, a2 as int, a3 as int)
    ensures 
        result as int >= 0,
        result as int == minimum_cost(a1 as int, a2 as int, a3 as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute max/min and prove equality to spec without external helpers */
    let max_val_i8: i8;
    if a1 >= a2 && a1 >= a3 {
        max_val_i8 = a1;
    } else if a2 >= a3 {
        max_val_i8 = a2;
    } else {
        max_val_i8 = a3;
    }

    let min_val_i8: i8;
    if a1 <= a2 && a1 <= a3 {
        min_val_i8 = a1;
    } else if a2 <= a3 {
        min_val_i8 = a2;
    } else {
        min_val_i8 = a3;
    }

    let diff_i8: i8 = max_val_i8 - min_val_i8;

    proof {
        let ai1: int = a1 as int;
        let ai2: int = a2 as int;
        let ai3: int = a3 as int;

        if ai1 >= ai2 && ai1 >= ai3 {
            assert((max_val_i8 as int) == ai1);
        } else if ai2 >= ai3 {
            assert((max_val_i8 as int) == ai2);
        } else {
            assert((max_val_i8 as int) == ai3);
        }

        if ai1 <= ai2 && ai1 <= ai3 {
            assert((min_val_i8 as int) == ai1);
        } else if ai2 <= ai3 {
            assert((min_val_i8 as int) == ai2);
        } else {
            assert((min_val_i8 as int) == ai3);
        }

        assert(max_of_three(ai1, ai2, ai3) == if ai1 >= ai2 && ai1 >= ai3 { ai1 } else if ai2 >= ai3 { ai2 } else { ai3 });
        assert(min_of_three(ai1, ai2, ai3) == if ai1 <= ai2 && ai1 <= ai3 { ai1 } else if ai2 <= ai3 { ai2 } else { ai3 });

        assert((max_val_i8 as int) == max_of_three(ai1, ai2, ai3));
        assert((min_val_i8 as int) == min_of_three(ai1, ai2, ai3));

        assert((diff_i8 as int) == minimum_cost(ai1, ai2, ai3));
    }

    diff_i8
}

// </vc-code>


}

fn main() {}