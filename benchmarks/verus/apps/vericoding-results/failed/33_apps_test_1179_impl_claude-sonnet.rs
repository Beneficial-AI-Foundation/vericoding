// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, l: Seq<int>) -> bool {
    n >= 1 && k >= 1 && l.len() == n && k <= n * (n + 1) / 2
}

spec fn total_identifiers_after_robot(i: int) -> int 
    recommends i >= 0
{
    i * (i + 1) / 2
}

spec fn correct_result(n: int, k: int, l: Seq<int>, result: int) -> bool
    recommends valid_input(n, k, l)
{
    exists|i: int| #[trigger] total_identifiers_after_robot(i) > 0 &&
      1 <= i <= n && 
      total_identifiers_after_robot(i - 1) < k <= total_identifiers_after_robot(i) &&
      result == l[k - total_identifiers_after_robot(i - 1) - 1]
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_total_identifiers_monotonic(i: int, j: int)
    requires i <= j
    ensures total_identifiers_after_robot(i) <= total_identifiers_after_robot(j)
{
}

proof fn lemma_total_identifiers_positive(i: int)
    requires i >= 1
    ensures total_identifiers_after_robot(i) > 0
{
}

/* helper modified by LLM (iteration 5): fixed proof lemma to be executable function */
fn lemma_find_robot_exists(n: int, k: int)
    requires n >= 1, k >= 1, k <= n * (n + 1) / 2
    ensures exists|i: int| 1 <= i <= n && total_identifiers_after_robot(i - 1) < k <= total_identifiers_after_robot(i)
{
    let mut i: int = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            total_identifiers_after_robot(i - 1) < k,
        decreases n - i
    {
        if total_identifiers_after_robot(i) >= k {
            return;
        }
        i = i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, l: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, l@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, k as int, l@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed unreachable macro call */
    proof {
        lemma_find_robot_exists(n as int, k as int);
    }
    
    let mut i: i8 = 1;
    let mut total_prev: i8 = 0;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            total_prev == total_identifiers_after_robot((i - 1) as int),
            total_prev < k,
        decreases n - i
    {
        let total_curr = total_prev + i;
        if total_curr >= k {
            let index = (k - total_prev - 1) as usize;
            proof {
                assert(total_identifiers_after_robot((i - 1) as int) < k as int <= total_identifiers_after_robot(i as int));
                assert(index < l.len());
            }
            return l[index];
        }
        total_prev = total_curr;
        i = i + 1;
    }
    
    0
}
// </vc-code>


}

fn main() {}