// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn wow_factor(s: Seq<char>) -> int {
    if s.len() < 4 { 0 }
    else {
        wow_factor_sum(s, 0)
    }
}

spec fn count_vv_pairs_before(s: Seq<char>, pos: int) -> int
    decreases pos
{
    if pos <= 1 { 0 }
    else {
        let prev = count_vv_pairs_before(s, pos - 1);
        if s[pos-1] == 'v' && s[pos-2] == 'v' { prev + 1 } else { prev }
    }
}

spec fn count_vv_pairs_after(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos
{
    if pos >= s.len() - 1 { 0 }
    else {
        let rest = count_vv_pairs_after(s, pos + 1);
        if pos + 1 < s.len() && s[pos] == 'v' && s[pos+1] == 'v' { rest + 1 } else { rest }
    }
}

spec fn wow_factor_sum(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos
{
    if pos >= s.len() { 0 }
    else {
        let current = if s[pos] == 'o' { 
            count_vv_pairs_before(s, pos) * count_vv_pairs_after(s, pos + 1)
        } else { 0 };
        current + wow_factor_sum(s, pos + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatches for int arithmetic */
fn lemma_count_vv_pairs_before_monotonic(s: Seq<char>, pos1: int, pos2: int)
    requires
        0 <= pos1 <= pos2 <= s.len(),
    ensures
        count_vv_pairs_before(s, pos1) <= count_vv_pairs_before(s, pos2),
    decreases pos2 - pos1
{
    if pos1 == pos2 {
        return;
    }
    lemma_count_vv_pairs_before_monotonic(s, pos1, pos2 - 1int);
}

fn lemma_count_vv_pairs_after_monotonic(s: Seq<char>, pos1: int, pos2: int)
    requires
        0 <= pos1 <= pos2 < s.len(),
    ensures
        count_vv_pairs_after(s, pos2) <= count_vv_pairs_after(s, pos1),
    decreases pos2 - pos1
{
    if pos1 == pos2 {
        return;
    }
    lemma_count_vv_pairs_after_monotonic(s, pos1 + 1int, pos2);
}

fn lemma_count_bounds(s: Seq<char>, pos: int)
    requires
        0 <= pos <= s.len(),
    ensures
        0 <= count_vv_pairs_before(s, pos) <= s.len(),
        0 <= count_vv_pairs_after(s, pos) <= s.len(),
    decreases s.len() - pos
{
    if pos <= 1int {
        return;
    }
    lemma_count_bounds(s, pos - 1int);
}

fn lemma_wow_factor_bounds(s: Seq<char>, pos: int)
    requires
        0 <= pos <= s.len(),
    ensures
        0 <= wow_factor_sum(s, pos) <= s.len() * s.len() * s.len(),
    decreases s.len() - pos
{
    if pos >= s.len() as int {
        return;
    }
    lemma_count_bounds(s, pos);
    lemma_wow_factor_bounds(s, pos + 1int);
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    ensures
        result as int == wow_factor(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches for int arithmetic */
    if s.len() < 4 {
        return 0;
    }
    
    let mut result: i32 = 0;
    
    for pos in 0..s.len() {
        if s[pos] == 'o' {
            let mut before_count: i32 = 0;
            let mut after_count: i32 = 0;
            
            // Count vv pairs before pos
            for i in 0..pos {
                if i > 0 && s[i-1] == 'v' && s[i] == 'v' {
                    before_count += 1;
                }
            }
            
            // Count vv pairs after pos
            for i in (pos+1)..s.len() {
                if i < s.len() - 1 && s[i] == 'v' && s[i+1] == 'v' {
                    after_count += 1;
                }
            }
            
            result += before_count * after_count;
        }
    }
    
    result as i8
}
// </vc-code>


}

fn main() {}