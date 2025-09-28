// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n && forall|i: int| 0 <= i < n ==> a[i] >= 0
}

spec fn count_survivors(n: int, a: Seq<int>) -> int {
    count_survivors_from(n, a, 0, n)
}

spec fn count_survivors_from(n: int, a: Seq<int>, start: int, left: int) -> int
    decreases n - start
{
    if start >= n {
        0
    } else {
        let i = n - 1 - start;
        let survives: int = if i < left { 1 } else { 0 };
        let new_left: int = if i - a[i] < left { i - a[i] } else { left };
        survives + count_survivors_from(n, a, start + 1, new_left)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures result >= 0 && result <= n && result as int == count_survivors(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion from `int` to `i8` by ensuring intermediate calculations are done with `int` before casting the final result to `i8`. */
    let ghost n_int = n as int;
    let ghost a_seq = a@.map_values(|x: i8| x as int);

    let mut survivors_count: i8 = 0;
    let mut left_to_survive: i8 = n;

    let mut i: i8 = (n as i8) - 1;

    while i >= 0
        invariant
            survivors_count as int >= 0,
            survivors_count as int <= (n - i) as int,
            left_to_survive as int >= 0,
            left_to_survive as int <= n as int,
            count_survivors_from(n_int, a_seq, (i + 1) as int, left_to_survive as int) == survivors_count as int,
            // loop variable i decreases, implies that the interval (i + 1) to n, increases.
            // ensuring that val_at_i is always non-negative as per problem statement and type handling.
            forall|j: int| (i + 1) <= j < n_int ==> a_seq[j] >= 0,
        decreases i
    {
        let ghost val_at_i_int = a_seq[i as int];

        if i < left_to_survive {
            survivors_count = survivors_count + 1;
        }

        let new_left_int: int = (i as int - val_at_i_int);
        let new_left_val: i8 = if new_left_int < 0 { 0 } else { new_left_int as i8 };

        if new_left_val < left_to_survive {
            left_to_survive = new_left_val;
        }

        i = i - 1;
    }

    survivors_count
}
// </vc-code>


}

fn main() {}