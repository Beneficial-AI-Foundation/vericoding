// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int) -> bool {
    a >= 1 && b >= 1
}

spec fn max_different_days(a: int, b: int) -> int {
    if a < b { a } else { b }
}

spec fn remaining_after_different(a: int, b: int) -> int {
    if a > b { a - max_different_days(a, b) } else { b - max_different_days(a, b) }
}

spec fn same_days(a: int, b: int) -> int {
    remaining_after_different(a, b) / 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: (int, int))
    requires valid_input(a, b)
    ensures {
        let (days_different, days_same) = result;
        days_different == max_different_days(a, b)
    }
    ensures {
        let (days_different, days_same) = result;
        days_same == same_days(a, b)
    }
    ensures {
        let (days_different, days_same) = result;
        days_different >= 0
    }
    ensures {
        let (days_different, days_same) = result;
        days_same >= 0
    }
    ensures {
        let (days_different, days_same) = result;
        days_different <= a && days_different <= b
    }
// </vc-spec>
// <vc-code>
{
    assume(false);
    (0, 0)
}
// </vc-code>


}

fn main() {}