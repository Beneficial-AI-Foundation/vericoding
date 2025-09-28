// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn vasya_eats_with_strategy(n: int, k: int) -> int
    decreases n
{
    if n <= 0 || k < 1 { 
        0 
    } else {
        let cur = if n < k { n } else { k };
        let remaining_after_vasya = n - cur;
        let remaining_after_petya = remaining_after_vasya - remaining_after_vasya / 10;
        cur + vasya_eats_with_strategy(remaining_after_petya, k)
    }
}

spec fn is_minimal_solution(n: int, k: int) -> bool {
    valid_input(n) && k >= 1 && 
    vasya_eats_with_strategy(n, k) * 2 >= n &&
    (k == 1 || vasya_eats_with_strategy(n, k - 1) * 2 < n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive implementation matching spec with named return */
fn vasya_eats_impl(n: int, k: int) -> (result: int)
    decreases n
    ensures
        result == vasya_eats_with_strategy(n, k),
{
    if n <= 0 || k < 1 {
        0
    } else {
        let cur = if n < k { n } else { k };
        let remaining_after_vasya = n - cur;
        let remaining_after_petya = remaining_after_vasya - remaining_after_vasya / 10;
        let rec = vasya_eats_impl(remaining_after_petya, k);
        cur + rec
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures
        1 <= result as int <= n as int,
        is_minimal_solution(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative search for minimal k using helper with loop invariants */
    let ni = n as int;
    let mut k: int = 1;

    while k < ni
        invariant
            1 <= k,
            k <= ni,
            forall j: int :: 1 <= j && j < k ==> vasya_eats_with_strategy(ni, j) * 2 < ni,
        decreases ni - k
    {
        let eaten = vasya_eats_impl(ni, k);
        proof {
            assert(eaten == vasya_eats_with_strategy(ni, k));
        }
        if eaten * 2 >= ni {
            return k as i8;
        }
        k = k + 1;
    }

    ni as i8
}
// </vc-code>


}

fn main() {}