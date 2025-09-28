// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_composite(x: int) -> bool {
    x >= 4 && exists|k: int| 2 <= k < x && #[trigger] (x % k) == 0
}

spec fn valid_input(queries: Seq<int>) -> bool {
    forall|i: int| 0 <= i < queries.len() ==> queries[i] >= 1
}

spec fn max_composite_summands(n: int) -> int {
    if n % 4 == 0 {
        n / 4
    } else if n % 4 == 1 && n / 4 >= 2 {
        n / 4 - 1
    } else if n % 4 == 2 && n / 4 >= 1 {
        n / 4
    } else if n % 4 == 3 && n / 4 >= 3 {
        n / 4 - 1
    } else {
        -1
    }
}

spec fn valid_result(queries: Seq<int>, results: Seq<int>) -> bool {
    results.len() == queries.len() &&
    forall|i: int| 0 <= i < queries.len() ==> results[i] == max_composite_summands(queries[i]) &&
    forall|i: int| 0 <= i < queries.len() ==> results[i] >= -1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute_max for i8 with proof of spec equivalence */
fn compute_max(n: i8) -> i8
    requires
        n >= 1,
    ensures
        (result as int) == max_composite_summands(n as int),
{
    let rem: i8 = n % 4;
    let q: i8 = n / 4;
    let res: i8;
    if rem == 0 {
        res = q;
    } else if rem == 1 {
        if q >= 2 {
            res = q - 1;
        } else {
            res = -1;
        }
    } else if rem == 2 {
        if q >= 1 {
            res = q;
        } else {
            res = -1;
        }
    } else {
        if q >= 3 {
            res = q - 1;
        } else {
            res = -1;
        }
    }
    proof {
        let ni: int = n as int;
        let expected: int = max_composite_summands(ni);
        let rem_i: int = ni % 4;
        let q_i: int = ni / 4;
        if rem_i == 0 {
            assert(expected == q_i);
            assert((res as int) == q as int);
            assert(q as int == q_i);
            assert((res as int) == expected);
        } else if rem_i == 1 {
            if q_i >= 2 {
                assert(expected == q_i - 1);
                assert((res as int) == (q as int) - 1);
                assert(q as int == q_i);
                assert((res as int) == expected);
            } else {
                assert(expected == -1);
                assert((res as int) == -1);
                assert((res as int) == expected);
            }
        } else if rem_i == 2 {
            if q_i >= 1 {
                assert(expected == q_i);
                assert((res as int) == q as int);
                assert(q as int == q_i);
                assert((res as int) == expected);
            } else {
                assert(expected == -1);
                assert((res as int) == -1);
                assert((res as int) == expected);
            }
        } else {
            if q_i >= 3 {
                assert(expected == q_i - 1);
                assert((res as int) == (q as int) - 1);
                assert(q as int == q_i);
                assert((res as int) == expected);
            } else {
                assert(expected == -1);
                assert((res as int) == -1);
                assert((res as int) == expected);
            }
        }
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn solve(queries: Vec<i8>) -> (results: Vec<i8>)
    requires valid_input(queries@.map(|i, x: i8| x as int))
    ensures valid_result(queries@.map(|i, x: i8| x as int), results@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate queries and compute per-query result using compute_max */
    let n = queries.len();
    let mut results_v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            (results_v@.len() as int) == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> (results_v@[j] as int) == max_composite_summands(queries@.map(|k, x: i8| x as int)@[j]),
        decreases n - i
    {
        let q: i8 = queries.get(i);
        let val: i8 = compute_max(q);
        results_v.push(val);
        i = i + 1;
    }
    results_v
}
// </vc-code>


}

fn main() {}