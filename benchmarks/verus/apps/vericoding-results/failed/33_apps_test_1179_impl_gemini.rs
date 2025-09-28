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
proof fn lemma_total_identifiers_is_monotonic(i: int, j: int)
    requires 0 <= i <= j
    ensures total_identifiers_after_robot(i) <= total_identifiers_after_robot(j)
    decreases j - i
{
    if i < j {
        lemma_total_identifiers_is_monotonic(i, j - 1);
    }
}

proof fn lemma_find_i_exists(n: int, k: int)
    requires
        n >= 1,
        k >= 1,
        k <= total_identifiers_after_robot(n),
    ensures
        exists|i: int| 1 <= i <= n &&
            total_identifiers_after_robot(i - 1) < k <= total_identifiers_after_robot(i),
    decreases n
{
    lemma_total_identifiers_is_monotonic(0, n);
    if n > 1 && k <= total_identifiers_after_robot(n - 1) {
        lemma_find_i_exists(n - 1, k);
    } else {
        let i = n;
        assert(1 <= i <= n);
        assert(total_identifiers_after_robot(i - 1) < k <= total_identifiers_after_robot(i));
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
    let n_int = n as int;
    let k_int = k as int;
    let l_view = l@.map(|_idx: int, x: i8| x as int);

    let mut i: int = 0;
    let mut total_ids: int = 0;
    while total_ids < k_int
        invariant
            0 <= i <= n_int,
            total_ids == total_identifiers_after_robot(i),
            valid_input(n_int, k_int, l_view),
        decreases n_int - i
    {
        lemma_total_identifiers_is_monotonic(i, n_int);
        assert(i < n_int) by {
            // from invariant: total_ids == total_identifiers_after_robot(i)
            // from loop condition: total_ids < k_int
            // from valid_input: k_int <= total_identifiers_after_robot(n_int)
            // So: total_identifiers_after_robot(i) < total_identifiers_after_robot(n_int)
            // By monotonicity, this implies i < n_int
        };
        i = i + 1;
        total_ids = total_ids + i;
    }

    let prev_total = total_identifiers_after_robot(i - 1);
    proof {
        lemma_total_identifiers_is_monotonic(i - 1, i - 1);
        lemma_find_i_exists(n_int, k_int);
        assert(total_identifiers_after_robot(i - 1) < k_int <= total_identifiers_after_robot(i));
    }

    let index = k_int - prev_total - 1;
    assert(0 <= index < l.view().len()) by {
        assert(k_int > prev_total);
        assert(index >= 0);
        assert(k_int <= total_ids);
        assert(k_int - prev_total <= i);
        assert(index <= i - 1);
        assert(i <= n_int);
        assert(i-1 < n_int);
    };

    let result = l[index as usize];
    assert(correct_result(n_int, k_int, l_view, result as int));
    result
}
// </vc-code>


}

fn main() {}