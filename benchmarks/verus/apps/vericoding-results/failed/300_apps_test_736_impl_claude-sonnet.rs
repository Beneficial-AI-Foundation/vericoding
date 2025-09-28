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
/* helper modified by LLM (iteration 5): added overflow bounds and cast safety */
proof fn lemma_min_moves_properties(n: int)
    requires n > 0
    ensures
        min_moves(n) <= n,
        min_moves(n) > 0,
        min_moves(n) == (n + 1) / 2
{
}

proof fn lemma_divisibility_search(n: int, m: int, start: int, end: int)
    requires
        valid_input(n, m),
        min_moves(n) <= start <= end <= n
    ensures
        (exists|k: int| start <= k <= end && #[trigger] (k % m) == 0) ||
        (forall|k: int| start <= k <= end ==> #[trigger] (k % m) != 0)
{
}

fn find_smallest_multiple(n: i8, m: i8) -> (result: i8)
    requires valid_input(n as int, m as int)
    ensures
        result == -1 || (min_moves(n as int) <= result as int <= n as int && result as int % m as int == 0),
        result != -1 ==> forall|k: int| (min_moves(n as int) <= k < result as int) ==> #[trigger] (k % m as int) != 0
{
    let min_required = if n % 2 == 0 { n / 2 } else { n / 2 + 1 };
    let mut i = min_required;
    
    while i <= n
        invariant
            min_required <= i <= n + 1,
            min_required == min_moves(n as int),
            i <= 127,
            forall|k: int| (min_required as int <= k < i as int) ==> #[trigger] (k % m as int) != 0
        decreases n - i
    {
        assert(i <= 127);
        assert(m > 0);
        if i % m == 0 {
            return i;
        }
        i = i + 1;
    }
    -1
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
    /* code modified by LLM (iteration 5): added overflow bounds and n > 0 assumptions */
    assert(n > 0);
    assert(n <= 127);
    
    let min_required = if n % 2 == 0 { n / 2 } else { n / 2 + 1 };
    
    let mut i = min_required;
    
    while i <= n
        invariant
            min_required <= i <= n + 1,
            min_required == min_moves(n as int),
            i <= 127,
            n > 0,
            forall|k: int| (min_required as int <= k < i as int) ==> #[trigger] (k % m as int) != 0
        decreases n - i
    {
        assert(i <= 127);
        assert(m > 0);
        assert(n > 0);
        if i % m == 0 {
            proof {
                assert(n > 0);
                assert(i as int % m as int == 0);
                assert(min_moves(n as int) <= i as int <= n as int);
                assert(valid_move_count(n as int, i as int));
                assert(is_valid_solution(n as int, m as int, i as int));
                assert(forall|k: int| (min_moves(n as int) <= k < i as int) ==> #[trigger] (k % m as int) != 0);
                assert(is_minimal_solution(n as int, m as int, i as int));
            }
            return i;
        }
        i = i + 1;
    }
    
    proof {
        assert(n > 0);
        assert(forall|k: int| min_moves(n as int) <= k <= n as int ==> #[trigger] (k % m as int) != 0);
        assert(no_smaller_solution(n as int, m as int, -1));
        assert(is_valid_solution(n as int, m as int, -1));
        assert(is_minimal_solution(n as int, m as int, -1));
    }
    
    -1
}
// </vc-code>


}

fn main() {}