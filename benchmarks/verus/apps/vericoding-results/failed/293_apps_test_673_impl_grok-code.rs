// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k > 0
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool 
    recommends k > 0
{
    result > n && result % k == 0 && forall|x: int| n < x < result ==> #[trigger] (x % k) != 0
}
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, k: int) -> bool 
{
    n >= 1 && k > 0
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool 
    recommends k > 0
{
    result > n && result % k == 0 && forall|x: int| n < x < result ==> #[trigger] (x % k) != 0
}

/* helper modified by LLM (iteration 5): Add #[trigger] annotation to forall quantifier in ensures */
fn next_multiple(n: i8, k: i8) -> (result: i8)
    requires
        n >= 1,
        k > 0,
    ensures
        result as int > n as int,
        (result as int) % (k as int) == 0,
        forall|x: int| (n as int) < x < (result as int) ==> #[trigger] (x % (k as int)) != 0,
{
    if n as int % k as int == 0 {
        n + k
    } else {
        let remainder = n as int % k as int;
        n + (k - remainder as i8)
    }
}

fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Ensure result computation and return */
{
    let result = next_multiple(n, k);
    result
}
// </vc-code>


}

fn main() {}