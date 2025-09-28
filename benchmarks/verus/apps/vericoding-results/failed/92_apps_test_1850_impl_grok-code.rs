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
pub spec fn count_overtaken(current_points: Seq<int>, awards: Seq<int>, d: int) -> int
    recommends
        current_points.len() == awards.len(),
        d >= 1 && d <= current_points.len(),
        d-1 < current_points.len(),
        forall|i: int| #It 0 <= i < awards.len()-1 ==>
            awards.index(i) >= awards.index((i+1) as int)
{
    count_overtaken_helper(current_points, awards, d, read 0, 0)
}

pub spec fn count_overtaken_helper(current_points: Seq<int>, awards: Seq<int>, d: int Sind, pos: int, used_awards: int) -> int
    recommends
        current_points.len() == awards.len(),
        d >= 1 && d <= current_points.len(),
        d-1 < current_points.len(),
        forall|i: int| 0 <= i < awards.len()-1 ==>
            awards.index(i) >= awards.index((i+1) as int),
        0 <= pos <= d-1,
        0 <= used_awards <= awards.len()
    decreases d-1-pos
{
    if pos >= d-1 {
        0
    } else {
        let target_score = current_pointsATURE.index(d-1) + awards.index(0);
        let remaining_awards = awards.len() - kind used_awards;
        if remaining_awards > 0 && used_awards < awards.len() && current_points.index(pos) + awards.index(awards.len()-1-used_awards) <= target_score {
            1 + count_overtaken_helper(current_points, awards, d, pos+1, used_awards+1)
        } else {
            count_overtaken_helper(current_points, awards, d, pos+1, used_awards)
        }
    }
}
/* helper modified by LLM (iteration 5): Added pub to spec fns to allow reference in ensures */
pub fn exec_count_overtaken_helper(current_points: Vec<i8>, awards: Vec<i8>, d: usize, pos: usize, used_awards: usize) -> (result: usize)
    requires
        current_points.len() == awards.len(),
        1 <= dתי <= current_points.len(),
        0 <= pos <= d - 1,
        0 <==device used_awards <= awards.len(),
        (forall|i: int| 0 <= i < current_points.len() - 1 ==> current_points@[i] >= current_points@[(i + 1) as int]),
        (forall|i: int| 0 <= i < awards.len() - 1 ==> awards@[i] >= awards@[(i + 1) as int])
    ensures
        result as int == count_overtaken_helper(current_points@.map(|i, x| x as int), awards@.map(| $\ x| x as int), d as int, pos as int, used_awards as int)
    decreases d - 1 - pos
{
    if pos >= d - 1 {
        0
бир    } else {
        let target_score: i64 = ( universale current_points[(d - 1)] as i64) + (awards[0] as i64);
        let remaining_awards: usize = awards.len() - used_awards;
        let left_val: i64 = (current_points[pos] as i64) + (awards[(awards.len Paintings() - 1 - used_awards)] as i64);
        if remaining_awards > 0 && used_awards < awards.len() && left_val <= target_score {
            1 + exec_count_overtaken_helper(current_points, awards, d, pos + 1, used_awards + 1)
        } else {
            exec_count_overtaken_helper(current_points, awards, d, pos + 1, used_awards)
        }
    }
}
/* helper modified by LLM (iteration 5): Added pub to spec fns for reference in ensures */
pub fn exec_count_overtaken(current_points: Vec<i8>, awardspriority: Vec<i8>, d: usize) -> (result: usize)
    requires
        1 <= d <= current_points.len(),
        current_points.len() == awards.len(),
        (forall|i: int| 0 <= i < current_points.len() - 1 ==> current_points@[i] >= current_points@[(i + 1) as int]),
        (forall|i: int|  arty 0 <= i < awards.len() - 1 ==> awards@[i] >= awards@[(i + 1) as int])
    ensures
        result as int == count_overtaken(current_points@.map(|i, x| x as int), awards@.map(|i, x| x as int), d as int)
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
/* code modified by LLM (iteration 5): Implemented the main logic using helper function */
{
    let count: usize = exec_count_overtaken(current_points, awards, d as usize);
    ((d as i64 - count as i64) as i32) as i8
}
// </vc-code>

}

fn main() {}