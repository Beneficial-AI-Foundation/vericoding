// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i] > 0
}

spec fn count_factors_of_two(n: int) -> int
    decreases n when n > 0
{
    if n > 0 && n % 2 == 0 { 1 + count_factors_of_two(n / 2) }
    else { 0 }
}

spec fn sum_factors(a: Seq<int>, i: int) -> int
    decreases a.len() - i when 0 <= i <= a.len()
{
    if 0 <= i < a.len() && (forall|j: int| 0 <= j < a.len() ==> a[j] > 0) {
        count_factors_of_two(a[i]) + sum_factors(a, i + 1)
    } else if i == a.len() {
        0
    } else {
        0
    }
}

spec fn max_operations(a: Seq<int>) -> int {
    if valid_input(a) { sum_factors(a, 0) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute_count as a proof function matching spec count_factors_of_two */
proof fn compute_count(n: int) -> (res: int)
    requires
        n > 0,
    ensures
        res == count_factors_of_two(n),
    decreases
        n when n > 0
{
    if n % 2 == 0 {
        let r = compute_count(n / 2);
        r + 1
    } else {
        0
    }
}

/* helper modified by LLM (iteration 5): compute_sum_vec as a proof function over Vec<i8> that mirrors sum_factors */
proof fn compute_sum_vec(a: Vec<i8>, i: int) -> (res: int)
    requires
        0 <= i <= a.len() as int,
        valid_input(a@.map(|k, x| x as int)),
    ensures
        res == sum_factors(a@.map(|k, x| x as int), i),
    decreases
        a.len() as int - i when 0 <= i <= a.len() as int
{
    if i == a.len() as int {
        0
    } else {
        let x: i8 = a.get(i as usize);
        let tail = compute_sum_vec(a, i + 1);
        compute_count(x as int) + tail
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(a@.map(|i, x| x as int)),
    ensures 
        result >= 0,
        result as int == max_operations(a@.map(|i, x| x as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute runtime total and prove it equals the spec sum via proof helpers */
    let mut total_runtime: i64 = 0;
    let mut idx: usize = 0;

    while idx < a.len()
        invariant
            0 <= idx as int <= a.len() as int,
            total_runtime as int + compute_sum_vec(a, idx as int) == compute_sum_vec(a, 0),
        decreases
            a.len() as int - idx as int
    {
        let x: i8 = a.get(idx);
        let mut v: i8 = x;
        let mut c: i64 = 0;

        while v > 0 && v % 2 == 0
            invariant
                0 <= c,
                v > 0,
                (c as int) + compute_count(v as int) == compute_count(x as int),
            decreases
                v as int
        {
            c += 1;
            v = v / 2;
        }

        proof {
            assert((c as int) + compute_count(v as int) == compute_count(x as int));
            assert(v > 0);
            assert(compute_count(v as int) == 0);
            assert(c as int == compute_count(x as int));
        }

        total_runtime += c;
        idx += 1;

        proof {
            assert(total_runtime as int + compute_sum_vec(a, idx as int) == compute_sum_vec(a, 0));
        }
    }

    proof {
        let tracked_total: int = compute_sum_vec(a, 0);
        assert(tracked_total == total_runtime as int);
        assert(tracked_total >= 0);
    }

    let result: i8 = total_runtime as i8;
    result
}

// </vc-code>


}

fn main() {}