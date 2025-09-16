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
/* helper modified by LLM (iteration 5): Added missing helper functions and lemmas */
spec fn is_prefix_at(string: Seq<char>, substring: Seq<char>, pos: int) -> bool {
    pos >= 0 && pos + substring.len() <= string.len() &&
    forall|k: int| 0 <= k < substring.len() ==> string[pos + k] == substring[k]
}

proof fn lemma_prefix_relationship(string: Seq<char>, substring: Seq<char>, pos: int)
    requires
        is_prefix_at(string, substring, pos),
    ensures
        substring.is_prefix_of(string.skip(pos)),
{
    assert(string.skip(pos).len() >= substring.len());
    assert(forall|k: int| 0 <= k < substring.len() ==> string.skip(pos)[k] == substring[k]);
}

proof fn lemma_how_many_times_bounds(string: Seq<char>, substring: Seq<char>)
    requires
        substring.len() >= 1,
    ensures
        how_many_times(string, substring) <= string.len(),
    decreases string.len(),
{
    if string.len() == 0 {
        assert(how_many_times(string, substring) == 0);
    } else {
        lemma_how_many_times_bounds(string.skip(1), substring);
        if substring.is_prefix_of(string) {
            assert(how_many_times(string, substring) == 1 + how_many_times(string.skip(1), substring));
            assert(how_many_times(string.skip(1), substring) <= string.skip(1).len());
            assert(string.skip(1).len() == string.len() - 1);
        } else {
            assert(how_many_times(string, substring) == how_many_times(string.skip(1), substring));
        }
    }
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
    /* code modified by LLM (iteration 5): Fixed loop invariants and added proof to relate count to spec */
    let mut i: usize = 0;
    let mut count: u32 = 0;
    
    proof {
        lemma_how_many_times_bounds(string@, substring@);
    }
    
    while i <= string.len()
        invariant
            i <= string.len(),
            substring.len() >= 1,
            count as nat == how_many_times(string@.take(i as int), substring@),
            count as nat <= i,
        decreases string.len() - i
    {
        if i == string.len() {
            break;
        }
        
        if substring.len() <= string.len() - i {
            let mut matches = true;
            let mut j: usize = 0;
            
            while j < substring.len()
                invariant
                    j <= substring.len(),
                    i < string.len(),
                    i + substring.len() <= string.len(),
                    matches == (forall|k: int| 0 <= k < j ==> string@[i as int + k] == substring@[k]),
                decreases substring.len() - j
            {
                if string[i + j] != substring[j] {
                    matches = false;
                    break;
                }
                j = j + 1;
            }
            
            if matches {
                proof {
                    assert(forall|k: int| 0 <= k < substring.len() ==> string@[i as int + k] == substring@[k]);
                    assert(is_prefix_at(string@, substring@, i as int));
                    lemma_prefix_relationship(string@, substring@, i as int);
                    assert(substring@.is_prefix_of(string@.skip(i as int)));
                }
                if count == u32::MAX {
                    return None;
                }
                count = count + 1;
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == string.len());
        assert(string@.take(i as int) == string@);
        assert(count as nat == how_many_times(string@, substring@));
    }
    
    Some(count)
}
// </vc-code>

}
fn main() {}