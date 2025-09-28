// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: int, v: Seq<int>) -> bool {
    n > 0 && v.len() == n && s >= 0 && forall|i: int| 0 <= i < v.len() ==> v[i] >= 0
}

spec fn sum(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        v[0] + sum(v.subrange(1, v.len() as int))
    }
}

spec fn min_seq(v: Seq<int>) -> int
    recommends v.len() > 0
    decreases v.len()
{
    if v.len() == 1 {
        v[0]
    } else if v.len() > 1 && v[0] <= min_seq(v.subrange(1, v.len() as int)) {
        v[0]
    } else if v.len() > 1 {
        min_seq(v.subrange(1, v.len() as int))
    } else {
        0
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma syntax by changing proof lemma to lemma */
lemma proof_min_seq_nonnegative(v: Seq<int>)
    requires
        v.len() > 0,
        forall|i: int| 0 <= i < v.len() ==> v[i] >= 0
    ensures
        min_seq(v) >= 0
{
    if v.len() == 1 {
        assert(min_seq(v) == v[0]);
    } else {
        let sub = v.subrange(1, v.len() as int);
        proof_min_seq_nonnegative(sub);
        assert(min_seq(v) == min(v[0], min_seq(sub)));
        assert(min(v[0], min_seq(sub)) >= 0);
    }
}

fn solve_helper(seq_v: Seq<int>, s_val: int, n_val: int) -> (diff: int)
    requires
        seq_v.len() == n_val,
        n_val > 0,
        s_val >= 0,
        forall|i: int| 0 <= i < seq_v.len() ==> seq_v[i] >= 0,
    ensures
        sum(seq_v) < s_val ==> diff == -1,
        sum(seq_v) >= s_val ==> diff == min((sum(seq_v) - s_val) / n_val, min_seq(seq_v)),
        diff == -1 || diff >= 0
{
    if sum(seq_v) < s_val {
        -1
    } else {
        let total = sum(seq_v);
        let remaining = total - s_val;
        proof_min_seq_nonnegative(seq_v);
        assert(min_seq(seq_v) >= 0);
        let avg_reduction = remaining / n_val;
        min(avg_reduction, min_seq(seq_v))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: i8, v: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, s as int, v@.map(|i, x| x as int))
    ensures 
        sum(v@.map(|i, x| x as int)) < s as int ==> result == -1,
        sum(v@.map(|i, x| x as int)) >= s as int ==> result == min((sum(v@.map(|i, x| x as int)) - s as int) / n as int, min_seq(v@.map(|i, x| x as int))) as i8,
        result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed, maintaining previous implementation */
    let seq_view = v@.map(|i, x| x as int);
    let result_val = solve_helper(seq_view, s as int, n as int);
    result_val as i8
}
// </vc-code>


}

fn main() {}