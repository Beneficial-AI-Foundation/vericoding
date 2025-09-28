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
proof fn lemma_count_overtaken_bounds(current_points: Seq<int>, awards: Seq<int>, d: int)
    requires
        current_points.len() == awards.len(),
        d >= 1 && d <= current_points.len(),
        d-1 < current_points.len(),
        forall|i: int| 0 <= i < awards.len()-1 ==> #[trigger] awards.index(i) >= awards.index((i+1) as int)
    ensures
        0 <= count_overtaken(current_points, awards, d) <= d-1
    decreases d
{
    /* helper modified by LLM (iteration 5): Added decreases clause */
    reveal(count_overtaken);
    if d == 1 {
        assert(count_overtaken(current_points, awards, d) == 0);
    } else {
        let target_score = current_points.index(d-1) + awards.index(0);
        let remaining_awards = awards.len() - 0;
        if remaining_awards > 0 && 0 < awards.len() && current_points.index(0) + awards.index(awards.len()-1-0) <= target_score {
            assert(count_overtaken(current_points, awards, d) == 1 + count_overtaken_helper(current_points, awards, d, 1, 1));
            lemma_count_overtaken_bounds(current_points, awards.subrange(0, awards.len() as int), d);
        } else {
            assert(count_overtaken(current_points, awards, d) == count_overtaken_helper(current_points, awards, d, 1, 0));
            lemma_count_overtaken_bounds(current_points, awards.subrange(0, awards.len() as int), d);
        }
    }
}

proof fn lemma_award_usage_property(current_points: Seq<int>, awards: Seq<int>, d: int, pos: int, used_awards: int)
    requires
        current_points.len() == awards.len(),
        d >= 1 && d <= current_points.len(),
        d-1 < current_points.len(),
        forall|i: int| 0 <= i < awards.len()-1 ==> #[trigger] awards.index(i) >= awards.index((i+1) as int),
        0 <= pos <= d-1,
        0 <= used_awards <= awards.len()
    ensures
        used_awards <= count_overtaken_helper(current_points, awards, d, pos, used_awards) + pos
    decreases d-1-pos
{
    /* helper modified by LLM (iteration 5): No changes needed */
    reveal(count_overtaken_helper);
    if pos >= d-1 {
        assert(count_overtaken_helper(current_points, awards, d, pos, used_awards) == 0);
        assert(used_awards <= pos);
    } else {
        let target_score = current_points.index(d-1) + awards.index(0);
        let remaining_awards = awards.len() - used_awards;
        if remaining_awards > 0 && used_awards < awards.len() && current_points.index(pos) + awards.index(awards.len()-1-used_awards) <= target_score {
            lemma_award_usage_property(current_points, awards.subrange(0, awards.len() as int), d, pos+1, used_awards+1);
            assert(used_awards <= (1 + count_overtaken_helper(current_points, awards, d, pos+1, used_awards+1)) + pos);
        } else {
            lemma_award_usage_property(current_points, awards.subrange(0, awards.len() as int), d, pos+1, used_awards);
            assert(used_awards <= count_overtaken_helper(current_points, awards, d, pos+1, used_awards) + pos);
        }
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
    /* code modified by LLM (iteration 5): Fixed verification errors */
    let d_i16 = d as i16;
    let target_score = current_points[d as usize - 1] as i16 + awards[0] as i16;
    let mut used_awards: i16 = 0;
    let mut overtaken: i16 = 0;
    let mut pos: i16 = 0;
    let awards_len = awards.len() as i16;
    
    while pos < d_i16 - 1
        invariant
            pos >= 0 && pos <= d_i16 - 1,
            used_awards >= 0 && used_awards <= awards_len,
            overtaken >= 0 && overtaken <= pos,
            overtaken == count_overtaken(current_points@.map(|i, x| x as int), awards@.map(|i, x| x as int), d as int)
        decreases (d_i16 - 1) - pos
    {
        let remaining_awards = awards_len - used_awards;
        let pos_usize = pos as usize;
        let used_awards_usize = used_awards as usize;
        
        if remaining_awards > 0 && used_awards < awards_len {
            let award_index = awards_len - 1 - used_awards;
            if award_index >= 0 && award_index < awards_len {
                let current_score = current_points[pos_usize] as i16 + awards[award_index as usize] as i16;
                if current_score <= target_score {
                    overtaken += 1;
                    used_awards += 1;
                }
            }
        }
        pos += 1;
    }
    
    (d_i16 - overtaken) as i8
}
// </vc-code>

}

fn main() {}