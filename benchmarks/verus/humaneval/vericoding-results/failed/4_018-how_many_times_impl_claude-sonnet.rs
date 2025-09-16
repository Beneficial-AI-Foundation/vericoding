// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn how_many_times(string: Seq<char>, substring: Seq<char>) -> (result:nat)
    decreases string.len(),
{
    if (string.len() == 0) {
        0
    } else if substring.is_prefix_of(string) {
        1 + how_many_times(string.skip(1), substring)
    } else {
        how_many_times(string.skip(1), substring)
    }
}

spec fn inner_expr_how_many_times_impl(opt_k: Option<u32>, string: Vec<char>, substring: Vec<char>) -> (result:bool) {
    match opt_k {
        Some(k) => k as nat == how_many_times(string@, substring@),
        None => how_many_times(string@, substring@) > u32::MAX,
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemmas for subrange properties and string matching */
proof fn lemma_how_many_times_monotonic(string: Seq<char>, substring: Seq<char>)
    requires substring.len() >= 1
    ensures how_many_times(string, substring) <= string.len()
    decreases string.len()
{
    if string.len() == 0 {
    } else if substring.is_prefix_of(string) {
        lemma_how_many_times_monotonic(string.skip(1), substring);
    } else {
        lemma_how_many_times_monotonic(string.skip(1), substring);
    }
}

proof fn lemma_subrange_take_equality(s: Seq<char>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures s.subrange(i, j) == s.skip(i).take(j - i)
{
}

proof fn lemma_how_many_times_step(string: Seq<char>, substring: Seq<char>, i: int)
    requires 
        substring.len() >= 1,
        0 <= i < string.len(),
        substring.is_prefix_of(string.skip(i))
    ensures 
        how_many_times(string.take(i + 1), substring) == how_many_times(string.take(i), substring) + 1
    decreases string.len()
{
}
// </vc-helpers>

// <vc-spec>
fn how_many_times_impl(string: Vec<char>, substring: Vec<char>) -> (opt_k: Option<u32>)

    requires
        substring.len() >= 1,

    ensures
        inner_expr_how_many_times_impl(opt_k, string, substring),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking and inner loop invariants */
    proof {
        lemma_how_many_times_monotonic(string@, substring@);
    }
    
    let mut count: u32 = 0;
    let mut i: usize = 0;
    
    while i < string.len()
        invariant
            count <= u32::MAX,
            i <= string.len(),
            count as nat == how_many_times(string@.take(i as int), substring@),
        decreases string.len() - i
    {
        if i < string.len() && substring.len() <= string.len() - i {
            let mut matches = true;
            let mut j: usize = 0;
            
            while j < substring.len() && matches
                invariant
                    j <= substring.len(),
                    i + substring.len() <= string.len(),
                    i + j < string.len(),
                    matches ==> string@.subrange(i as int, i as int + j as int) == substring@.take(j as int),
                decreases substring.len() - j
            {
                if string[i + j] != substring[j] {
                    matches = false;
                } else {
                    j += 1;
                }
            }
            
            if matches && j == substring.len() {
                if count == u32::MAX {
                    return None;
                }
                count += 1;
            }
        }
        i += 1;
    }
    
    Some(count)
}
// </vc-code>

}
fn main() {}