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
    let d_idx = (d - 1) as usize;
    let target_score = current_points[d_idx] + awards[0];
    let mut overtaken: i8 = 0;
    let mut award_idx: usize = awards.len() - 1;
    let mut pos: usize = 0;
    
    while pos < d_idx
        invariant
            0 <= pos <= d_idx,
            award_idx + overtaken as usize == awards.len() - 1,
            overtaken >= 0,
            overtaken as int == count_overtaken_helper(current_points@.map(|i, x| x as int), awards@.map(|i, x| x as int), d as int, 0, 0) - count_overtaken_helper(current_points@.map(|i, x| x as int), awards@.map(|i, x| x as int), d as int, pos as int, overtaken as int),
            overtaken as int <= pos as int,
            overtaken as int <= d as int - 1,
            award_idx < awards.len(),
        decreases d_idx - pos
    {
        if overtaken < (d - 1) && current_points[pos] + awards[award_idx] <= target_score {
            overtaken = overtaken + 1;
            if award_idx > 0 {
                award_idx = award_idx - 1;
            }
        }
        pos = pos + 1;
    }
    
    let result = d - overtaken;
    result
}
// </vc-code>

}

fn main() {}