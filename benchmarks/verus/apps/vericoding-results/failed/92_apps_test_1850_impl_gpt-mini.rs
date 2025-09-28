// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int, d: int, current_points: Seq<int>, awards: Seq<int>) -> bool {
        n >= 1 && n <= 200000 &&
        d >= 1 && d <= n &&
        current_points.len() == n &&
        awards.len() == n &&
        d-1 < current_points.len() &&
        (forall|i: int| 0 <= i < current_points.len()-1 ==> 
            #[trigger] current_points.index(i) >= current_points.index((i+1) as int)) &&
        (forall|i: int| 0 <= i < awards.len()-1 ==> 
            #[trigger] awards.index(i) >= awards.index((i+1) as int))
    }
    
    spec fn count_overtaken(current_points: Seq<int>, awards: Seq<int>, d: int) -> int
        recommends 
            current_points.len() == awards.len(),
            d >= 1 && d <= current_points.len(),
            d-1 < current_points.len(),
            forall|i: int| 0 <= i < awards.len()-1 ==> 
                #[trigger] awards.index(i) >= awards.index((i+1) as int)
    {
        count_overtaken_helper(current_points, awards, d, 0, 0)
    }
    
    spec fn count_overtaken_helper(current_points: Seq<int>, awards: Seq<int>, d: int, pos: int, used_awards: int) -> int
        recommends 
            current_points.len() == awards.len(),
            d >= 1 && d <= current_points.len(),
            d-1 < current_points.len(),
            forall|i: int| 0 <= i < awards.len()-1 ==> 
                #[trigger] awards.index(i) >= awards.index((i+1) as int),
            0 <= pos <= d-1,
            0 <= used_awards <= awards.len()
        decreases d-1-pos
    {
        if pos >= d-1 {
            0
        } else {
            let target_score = current_points.index(d-1) + awards.index(0);
            let remaining_awards = awards.len() - used_awards;
            if remaining_awards > 0 && used_awards < awards.len() && current_points.index(pos) + awards.index(awards.len()-1-used_awards) <= target_score {
                1 + count_overtaken_helper(current_points, awards, d, pos+1, used_awards+1)
            } else {
                count_overtaken_helper(current_points, awards, d, pos+1, used_awards)
            }
        }
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable helper mirroring spec count_overtaken_helper */
fn exec_count_overtaken_helper(current_points: &Vec<i8>, awards: &Vec<i8>, d: i8, pos: i8, used_awards: i8) -> i8
    requires
        current_points.len() == awards.len(),
        1 <= d && d <= current_points.len() as i8,
        0 <= pos && pos <= d-1,
        0 <= used_awards && used_awards <= awards.len() as i8,
    decreases
        d as int - 1 - pos as int,
    ensures
        result as int == count_overtaken_helper(current_points@.map(|_, x| x as int), awards@.map(|_, x| x as int), d as int, pos as int, used_awards as int),
{
    if pos >= d-1 {
        0i8
    } else {
        let idx_d_1 = (d - 1) as usize;
        let target_score: int = current_points[idx_d_1] as int + awards[0] as int;
        let remaining_awards: i8 = awards.len() as i8 - used_awards;
        let last_award_idx_i8 = awards.len() as i8 - 1 - used_awards;
        if remaining_awards > 0 && used_awards < awards.len() as i8 {
            let pos_idx = pos as usize;
            let last_idx = last_award_idx_i8 as usize;
            if (current_points[pos_idx] as int + awards[last_idx] as int) <= target_score {
                1i8 + exec_count_overtaken_helper(current_points, awards, d, pos + 1, used_awards + 1)
            } else {
                exec_count_overtaken_helper(current_points, awards, d, pos + 1, used_awards)
            }
        } else {
            exec_count_overtaken_helper(current_points, awards, d, pos + 1, used_awards)
        }
    }
}

/* helper modified by LLM (iteration 5): bridge helper to start recursion for Vec inputs */
fn exec_count_overtaken_vec(current_points: &Vec<i8>, awards: &Vec<i8>, d: i8) -> i8
    requires
        current_points.len() == awards.len(),
        1 <= d && d <= current_points.len() as i8,
    ensures
        result as int == count_overtaken(current_points@.map(|_, x| x as int), awards@.map(|_, x| x as int), d as int),
{
    exec_count_overtaken_helper(current_points, awards, d, 0, 0)
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, current_points: Vec<i8>, awards: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, d as int, current_points@.map(|i, x| x as int), awards@.map(|i, x| x as int))
    ensures 
        1 <= result as int <= d as int,
        result as int == d as int - count_overtaken(current_points@.map(|i, x| x as int), awards@.map(|i, x| x as int), d as int)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): compute result using exec_count_overtaken_vec */
    let cnt: i8 = exec_count_overtaken_vec(&current_points, &awards, d);
    let result: i8 = d - cnt;
    result
}

// </vc-code>

}

fn main() {}