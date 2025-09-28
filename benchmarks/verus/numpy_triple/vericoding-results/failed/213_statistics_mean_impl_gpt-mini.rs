// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive proof that if all elements equal, vec_sum equals value * len */
proof fn all_equal_implies_sum(a: Seq<i32>)
    requires
        a.len() > 0,
        all_equal(a),
    ensures
        vec_sum(a) == (a[0] as int) * (a.len() as int),
    decreases a.len()
{
    if a.len() == 1 {
        proof {
            assert(vec_sum(a) == a[0] as int);
        }
    } else {
        let rest = a.skip(1);
        proof {
            assert(all_equal(rest));
            all_equal_implies_sum(rest);
            assert(vec_sum(a) == (a[0] as int) + vec_sum(rest));
            assert(vec_sum(rest) == (rest[0] as int) * (rest.len() as int));
            assert(rest[0] == a[0]);
            assert(vec_sum(a) == (a[0] as int) + (a[0] as int) * (rest.len() as int));
            assert(vec_sum(a) == (a[0] as int) * (a.len() as int));
        }
    }
}

/* helper modified by LLM (iteration 5): spec for prefix sum of a sequence */
spec fn vec_sum_prefix(a: Seq<i32>, n: int) -> int
    requires
        0 <= n <= a.len(),
    decreases n
{
    if n == 0 {
        0
    } else {
        a[0] as int + vec_sum_prefix(a.skip(1), n - 1)
    }
}

/* helper modified by LLM (iteration 5): proof that prefix sum for full length equals vec_sum */
proof fn vec_sum_prefix_full(a: Seq<i32>)
    ensures
        vec_sum_prefix(a, a.len() as int) == vec_sum(a),
    decreases a.len()
{
    if a.len() == 0 {
        proof {
            assert(vec_sum_prefix(a, 0) == 0);
            assert(vec_sum(a) == 0);
        }
    } else {
        proof {
            vec_sum_prefix_full(a.skip(1));
            assert(vec_sum_prefix(a, a.len() as int) == (a[0] as int) + vec_sum_prefix(a.skip(1), (a.len() - 1) as int));
            assert(vec_sum(a) == (a[0] as int) + vec_sum(a.skip(1)));
            assert(vec_sum_prefix(a.skip(1), (a.len() - 1) as int) == vec_sum(a.skip(1)));
            assert(vec_sum_prefix(a, a.len() as int) == vec_sum(a));
        }
    }
}

// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        a[0] as int + vec_sum(a.skip(1))
    }
}

spec fn all_equal(a: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]
}

fn mean(a: Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures 
        /* Core property: mean * count == sum */
        (result as int) * (a.len() as int) == vec_sum(a@),
        /* For constant vectors, mean equals the constant */
        all_equal(a@) ==> result == a[0]
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): compute executable sum over Vec, use ghost variable to track spec prefix sum and apply lemma for all-equal case */
    let mut sum_exe: i32 = 0;
    let mut k: usize = 0;
    let ghost mut gs: int = 0;
    while k < a.len()
        invariant
            0 <= (k as int) && (k as int) <= (a.len() as int),
            gs == vec_sum_prefix(a@, k as int),
            (sum_exe as int) == gs,
        decreases a.len() - k
    {
        sum_exe = sum_exe + a[k];
        gs = gs + (a@[k as int] as int);
        k = k + 1;
    }

    if all_equal(a@) {
        proof {
            all_equal_implies_sum(a@);
        }
        a[0]
    } else {
        let res: i32 = sum_exe / (a.len() as i32);
        proof {
            assert(gs == vec_sum_prefix(a@, a.len() as int));
            vec_sum_prefix_full(a@);
            assert(gs == vec_sum(a@));
            assert((res as int) * (a.len() as int) == vec_sum(a@));
        }
        res
    }
}

// </vc-code>


}
fn main() {}