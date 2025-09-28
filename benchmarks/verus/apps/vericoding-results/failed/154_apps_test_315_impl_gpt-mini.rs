// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}

spec fn valid_input(n: int, k: int, a: Seq<int>) -> bool
{
    n >= 1 && a.len() == n && k >= 0 && forall|i: int| 0 <= i < n ==> #[trigger] a[i] >= 0
}

spec fn valid_output(a: Seq<int>, final_schedule: Seq<int>, additional_walks: int, k: int) -> bool
{
    final_schedule.len() == a.len() &&
    additional_walks >= 0 &&
    forall|i: int| 0 <= i < a.len() ==> #[trigger] final_schedule[i] >= a[i] &&
    forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] final_schedule[i] + final_schedule[i + 1] >= k &&
    additional_walks == sum(final_schedule) - sum(a)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): lemma that updating one element changes sum by delta */
proof fn sum_single_change(old: Seq<int>, idx: int, delta: int, new: Seq<int>)
    requires
        old.len() == new.len(),
        0 <= idx && idx < old.len(),
        forall|j: int| 0 <= j && j < old.len() && j != idx ==> new[j] == old[j],
        new[idx] == old[idx] + delta,
    ensures
        sum(new) == sum(old) + delta,
    decreases
        old.len()
{
    assert(forall|j: int| 0 <= j && j < old.len() && j != idx ==> new[j] - old[j] == 0);
    assert(new[idx] - old[idx] == delta);
    reveal(sum);
    assert(sum(new) == sum(old) + delta);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: (i8, Vec<i8>))
    requires valid_input(n as int, k as int, a@.map_values(|x: i8| x as int))
    ensures valid_output(a@.map_values(|x: i8| x as int), result.1@.map_values(|x: i8| x as int), result.0 as int, k as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): greedy construction of final_schedule and additional walks using runtime integers and a proof block to establish the spec */
{
    let n_usize = n as usize;
    let k_i64 = k as i64;
    let mut res = Vec::<i8>::new();
    res.reserve(n_usize);
    let mut added_i64: i64 = 0;
    let mut idx: usize = 0;
    while idx < n_usize {
        let ai_i64 = a[idx] as i64;
        if idx == 0 {
            res.push(ai_i64 as i8);
        } else {
            let prev = res[idx - 1] as i64;
            let need = k_i64 - prev;
            let mut inc: i64 = 0;
            if need > ai_i64 {
                inc = need - ai_i64;
            }
            res.push((ai_i64 + inc) as i8);
            added_i64 += inc;
        }
        idx += 1;
    }

    proof {
        // Move runtime values into ghost/spec level for verification
        let n_int = n as int;
        let k_int = k as int;
        let final_s: Seq<int> = res@.map_values(|x: i8| x as int);
        let a_s: Seq<int> = a@.map_values(|x: i8| x as int);
        let added_int: int = added_i64 as int;

        // lengths
        assert(final_s.len() as int == n_int);
        assert(a_s.len() as int == n_int);
        assert(final_s.len() == a_s.len());

        // each final element is at least the original (by construction)
        let mut j: int = 0;
        while j < n_int
            invariant
                0 <= j && j <= n_int,
            decreases n_int - j
        {
            if j == 0 {
                assert(final_s[0] == a_s[0]);
            } else {
                let prev = final_s[j - 1];
                let ai = a_s[j];
                if k_int - prev > ai {
                    assert(final_s[j] == k_int - prev);
                    assert(k_int - prev >= ai);
                } else {
                    assert(final_s[j] == ai);
                }
                assert(final_s[j] >= ai);
            }
            j = j + 1;
        }

        // adjacent sums >= k
        let mut t: int = 0;
        while t < n_int - 1
            invariant
                0 <= t && t <= n_int,
            decreases n_int - 1 - t
        {
            assert(final_s[t] + final_s[t + 1] >= k_int);
            t = t + 1;
        }

        // additional_walks equals sum(final) - sum(a)
        reveal(sum);
        assert(sum(final_s) - sum(a_s) == added_int);

        // non-negativity
        assert(added_int >= 0);
    }

    (added_i64 as i8, res)
}

// </vc-code>


}

fn main() {}