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
fn compute_sum(v: Vec<i8>) -> (result: i64)
    requires v@.len() > 0
    ensures result as int == sum(v@.map(|i, x| x as int))
    decreases v@.len()
{
    if v.len() == 1 {
        v[0] as i64
    } else {
        let sub = v.slice(1, v.len());
        (v[0] as i64) + compute_sum(sub)
    }
}

/* helper modified by LLM (iteration 5): Fixed compilation by using vec.slice instead of invalid subrange */
fn compute_min_seq(v: Vec<i8>) -> (result: i64)
    requires v@.len() > 0
    ensures result as int == min_seq(v@.map(|i, x| x as int))
    decreases v@.len()
{
    if v.len() == 1 {
        v[0] as i64
    } else if v.len() > 1 {
        let sub = v.slice(1, v.len());
        let tail_min = compute_min_seq(sub);
        compute_min(v[0] as i64, tail_min)
    } else {
        0
    }
}

/* helper modified by LLM (iteration 4): Renamed min to compute_min to avoid naming conflict with spec fn */
fn compute_min(a: i64, b: i64) -> i64 {
    if a <= b { a } else { b }
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
    /* code modified by LLM (iteration 5): No changes needed after helper fixes */
    let sum_v = compute_sum(v);
    let min_v = compute_min_seq(v);
    proof {
        assert(sum(v@.map(|i, x| x as int)) == sum_v as int);
        assert(min_seq(v@.map(|i, x| x as int)) == min_v as int);
    }
    if sum_v < (s as i64) {
        -1i8
    } else {
        let excess = sum_v - (s as i64);
        let adjustment = excess / (n as i64);
        let to_add = compute_min(adjustment, min_v);
        proof {
            assert(to_add as int == min((sum_v as int - s as int) / n as int, min_v as int));
        }
        to_add as i8
    }
}
// </vc-code>


}

fn main() {}