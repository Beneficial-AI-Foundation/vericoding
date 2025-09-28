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
/* helper modified by LLM (iteration 5): fixed int literal syntax errors */
fn lemma_count_overtaken_bounds(current_points: Seq<int>, awards: Seq<int>, d: int)
    requires
        current_points.len() == awards.len(),
        d >= 1 && d <= current_points.len(),
        d-1 < current_points.len(),
        forall|i: int| 0 <= i < awards.len()-1 ==> 
            #[trigger] awards.index(i) >= awards.index((i+1) as int)
    ensures
        0 <= count_overtaken(current_points, awards, d) <= d-1
{
    lemma_count_overtaken_helper_bounds(current_points, awards, d, 0, 0);
}

fn lemma_count_overtaken_helper_bounds(current_points: Seq<int>, awards: Seq<int>, d: int, pos: int, used_awards: int)
    requires
        current_points.len() == awards.len(),
        d >= 1 && d <= current_points.len(),
        d-1 < current_points.len(),
        forall|i: int| 0 <= i < awards.len()-1 ==> 
            #[trigger] awards.index(i) >= awards.index((i+1) as int),
        0 <= pos <= d-1,
        0 <= used_awards <= awards.len()
    ensures
        0 <= count_overtaken_helper(current_points, awards, d, pos, used_awards) <= d-1-pos
    decreases d-1-pos
{
    if pos >= d-1 {
        // base case
    } else {
        lemma_count_overtaken_helper_bounds(current_points, awards, d, pos+1, used_awards);
        lemma_count_overtaken_helper_bounds(current_points, awards, d, pos+1, used_awards+1);
    }
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
    /* code modified by LLM (iteration 5): simplified implementation to compute result directly */
    let target_score = current_points[(d-1) as usize] + awards[0];
    let mut overtaken = 0i8;
    let mut pos = 0usize;
    let mut used_awards = 0usize;
    
    while pos < (d-1) as usize
        invariant
            pos <= (d-1) as usize,
            used_awards <= awards.len(),
            0 <= overtaken <= pos as i8
        decreases (d-1) as usize - pos
    {
        let remaining_awards = awards.len() - used_awards;
        if remaining_awards > 0 && used_awards < awards.len() && current_points[pos] + awards[awards.len()-1-used_awards] <= target_score {
            overtaken += 1;
            used_awards += 1;
        }
        pos += 1;
    }
    
    proof {
        lemma_count_overtaken_bounds(current_points@.map(|i, x| x as int), awards@.map(|i, x| x as int), d as int);
    }
    
    d - overtaken
}
// </vc-code>

}

fn main() {}