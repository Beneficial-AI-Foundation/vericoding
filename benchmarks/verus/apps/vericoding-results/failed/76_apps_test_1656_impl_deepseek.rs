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
/* helper modified by LLM (iteration 5): fixed proof function syntax and added proper proof helpers */
proof fn wow_factor_sum_rec_eq(s: Seq<char>, pos: nat) -> (sum: int)
    requires
        pos <= s.len(),
    ensures
        sum == wow_factor_sum(s, pos as int),
    decreases s.len() - pos
{
    if pos >= s.len() {
        0
    } else {
        let current = if s[pos] == 'o' {
            count_vv_pairs_before(s, pos as int) * count_vv_pairs_after(s, (pos + 1) as int)
        } else {
            0
        };
        current + wow_factor_sum_rec_eq(s, pos + 1)
    }
}

proof fn wow_factor_equivalence()
    ensures
        forall |s: Seq<char>| wow_factor(s) == wow_factor_sum(s, 0)
{
    assert forall |s: Seq<char>| wow_factor(s) == wow_factor_sum(s, 0) by {
        if s.len() < 4 {
            assert(wow_factor(s) == 0);
            assert(wow_factor_sum(s, 0) == 0);
        } else {
            assert(wow_factor(s) == wow_factor_sum(s, 0));
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    ensures
        result as int == wow_factor(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed missing closing brace in while loop */
{
    if s.len() < 4 {
        return 0;
    }
    
    let mut before_counts = vec![0; s.len()];
    let mut after_counts = vec![0; s.len()];
    let mut result: i8 = 0;
    
    proof {
        wow_factor_equivalence();
    }
    
    for i in 0..s.len() {
        if i >= 2 {
            before_counts[i] = before_counts[i - 1];
            if s[i - 1] == 'v' && s[i - 2] == 'v' {
                before_counts[i] += 1;
            }
        }
    }
    
    let mut i = (s.len() - 1) as i64;
    while i >= 0
        invariant
            after_counts[i as usize] == count_vv_pairs_after(s@, i as int),
            i >= -1,
        decreases i
    {
        if i < (s.len() - 1) as i64 {
            after_counts[i as usize] = after_counts[(i + 1) as usize];
            if i >= 0 && i < (s.len() - 1) as i64 && s[i as usize] == 'v' && s[(i + 1) as usize] == 'v' {
                after_counts[i as usize] += 1;
            }
        }
        i -= 1;
    }
    
    for i in 0..s.len() {
        if s[i] == 'o' && i >= 2 && i < s.len() - 1 {
            let before = before_counts[i] as i8;
            let after = after_counts[i + 1] as i8;
            result += before * after;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}