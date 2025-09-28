// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    n > 0 && n <= 10000 && m > 1 && m <= 10
}

spec fn min_moves(n: int) -> int
    recommends n > 0
{
    if n % 2 == 0 { n / 2 } else { n / 2 + 1 }
}

spec fn valid_move_count(n: int, k: int) -> bool
    recommends n > 0
{
    min_moves(n) <= k <= n
}

spec fn is_valid_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result == -1 || (result > 0 && result % m == 0 && valid_move_count(n, result))
}

spec fn no_smaller_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result == -1 ==> forall|k: int| min_moves(n) <= k <= n ==> #[trigger] (k % m) != 0
}

spec fn is_minimal_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result != -1 ==> forall|k: int| (min_moves(n) <= k <= n && k < result) ==> #[trigger] (k % m) != 0
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_for_all_less_than_min_moves_invalid(n: int, m: int) -> (result: int)
    requires
        n > 0,
        m > 1,
        forall|k: int| min_moves(n) <= k <= n ==> #[trigger] (k % m) != 0
    ensures
        result == -1
{
    -1
}

proof fn lemma_find_minimal_solution(n: int, m: int, start: int) -> (result: int)
    requires
        n > 0,
        m > 1,
        min_moves(n) <= start <= n,
        (start % m) == 0
    ensures
        result == start
{
    start
}

spec fn find_first_valid_move(n: int, m: int) -> int
    recommends n > 0 && m > 1
{
    let min_move = min_moves(n);
    if exists|k: int| #[trigger] (k % m == 0) && min_move <= k && k <= n {
        choose|k: int| #[trigger] (k % m == 0) && min_move <= k && k <= n
    } else {
        -1
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int)
    ensures 
        is_valid_solution(n as int, m as int, result as int) &&
        no_smaller_solution(n as int, m as int, result as int) &&
        is_minimal_solution(n as int, m as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed trigger annotation for exists quantifier */
    let min_move = if n % 2 == 0 { n / 2 } else { n / 2 + 1 };
    
    let mut candidate = min_move;
    
    while candidate <= n
        invariant
            min_move <= candidate <= n + 1,
            forall|k: i8| min_move <= k < candidate ==> #[trigger] (k as int % m as int) != 0
        decreases (n - candidate) as int
    {
        if candidate % m == 0 {
            return candidate;
        }
        candidate += 1;
    }
    
    -1
}
// </vc-code>


}

fn main() {}