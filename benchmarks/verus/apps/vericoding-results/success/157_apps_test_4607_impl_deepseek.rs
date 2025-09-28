// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 12 && 1 <= b <= 31
}

spec fn takahashi_count(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    if a > b { a - 1 } else { a }
}
// </vc-preamble>

// <vc-helpers>

proof fn takahashi_count_lemma(a: int, b: int)
    requires valid_input(a, b)
    ensures takahashi_count(a, b) == (if a > b { a - 1 } else { a })
{
}

proof fn solve_lemma(a: i8, b: i8, result: i8)
    requires
        valid_input(a as int, b as int),
        (a > b ==> result as int == a as int - 1),
        (a <= b ==> result as int == a as int)
    ensures
        result as int == takahashi_count(a as int, b as int)
{
    takahashi_count_lemma(a as int, b as int);
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures 
        result as int == takahashi_count(a as int, b as int) &&
        (a > b ==> result as int == a as int - 1) &&
        (a <= b ==> result as int == a as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): simplified implementation with lemma usage */
    let result_value = if a > b { a - 1 } else { a };
    proof {
        solve_lemma(a, b, result_value);
    }
    result_value
}
// </vc-code>


}

fn main() {}