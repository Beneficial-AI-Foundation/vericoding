// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int, w: Seq<int>) -> bool {
    k > 0 && n >= 0 && w.len() == n && forall|i: int| 0 <= i < w.len() ==> w[i] >= 0
}

spec fn sum_trips(w: Seq<int>, k: int) -> int
    decreases w.len()
{
    if w.len() == 0 {
        0
    } else {
        (w[0] + k - 1) / k + sum_trips(w.drop_first(), k)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): sum_prefix and lemma relating it to sum_trips */
spec fn sum_prefix(s: Seq<int>, k: int, m: nat) -> int
    requires
        m <= s.len(),
    decreases m
{
    if m == 0 {
        0
    } else {
        (s@[0] + k - 1) / k + sum_prefix(s.drop_first(), k, m - 1)
    }
}

proof fn sum_prefix_eq_sum_trips(s: Seq<int>, k: int, m: nat)
    requires
        k > 0,
        m <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> s@[i] >= 0,
    ensures
        sum_prefix(s, k, m) == sum_trips(s.take(m), k),
{
    if m == 0 {
        proof {
            assert(sum_prefix(s, k, 0) == 0);
            assert(sum_trips(s.take(0), k) == 0);
        }
    } else {
        proof {
            assert(sum_prefix(s, k, m) == (s@[0] + k - 1) / k + sum_prefix(s.drop_first(), k, m - 1));
            assert(sum_trips(s.take(m), k) == (s.take(m)@[0] + k - 1) / k + sum_trips(s.take(m).drop_first(), k));
            assert(s.take(m)@[0] == s@[0]);
            assert(s.take(m).drop_first() == s.drop_first().take(m - 1));
            sum_prefix_eq_sum_trips(s.drop_first(), k, m - 1);
            assert(sum_prefix(s.drop_first(), k, m - 1) == sum_trips(s.drop_first().take(m - 1), k));
            assert(sum_trips(s.drop_first().take(m - 1), k) == sum_trips(s.take(m).drop_first(), k));
            assert(sum_prefix(s, k, m) == sum_trips(s.take(m), k));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, w: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, k as int, w@.map_values(|v: i8| v as int)),
    ensures 
        result >= 0,
        result as int == (sum_trips(w@.map_values(|v: i8| v as int), k as int) + 1) / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute runtime total and prove equality in proof block */
    let mut total_i32: i32 = 0;
    let k_i32: i32 = k as i32;
    let len_usize: usize = w.len();
    let mut idx: usize = 0usize;
    while idx < len_usize {
        let vi: i8 = w.get(idx);
        total_i32 = total_i32 + ((vi as i32 + k_i32 - 1) / k_i32);
        idx = idx + 1;
    }
    let res_i32: i32 = (total_i32 + 1) / 2;
    proof {
        let s: Seq<int> = w@.map_values(|v: i8| v as int);
        let k_int: int = k as int;
        sum_prefix_eq_sum_trips(s, k_int, s.len());
        assert((res_i32 as int) == (sum_trips(s, k_int) + 1) / 2);
    }
    res_i32 as i8
}

// </vc-code>


}

fn main() {}