// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 1
}

spec fn count_distinct_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>
proof fn seq_to_set_preserves_unique(s: Seq<char>)
    ensures
        is_unique(s) <==> count_distinct_chars(s) == s.len() as int
{
    assert(s.to_set().len() as int == count_distinct_chars(s));
    assert(is_unique(s) ==> count_distinct_chars(s) == s.len() as int);
    assert(count_distinct_chars(s) == s.len() as int ==> is_unique(s));
}

spec fn is_unique(s: Seq<char>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

proof fn map_empty_lemma() 
    ensures 
        vstd::map::Map::<char, bool>::empty().dom().finite()
{
}

proof fn ghost_empty_map() -> (ghost_seen: Map<char, bool>)
    ensures
        ghost_seen.dom().finite()
{
    vstd::map::Map::<char, bool>::empty()
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: i32)
    requires 
        valid_input(n as int, s@)
    ensures 
        n > 26 ==> result == -1,
        n <= 26 ==> result >= 0 && result < n as i32,
        n <= 26 ==> result == s@.len() as i32 - count_distinct_chars(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ghost map initialization syntax */
    proof {
        seq_to_set_preserves_unique(s@);
        map_empty_lemma();
    }
    
    if n > 26 {
        -1
    } else {
        let mut distinct_count: usize = 0;
        let ghost_seen = ghost_empty_map();
        let mut seen = ghost_seen;
        
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                distinct_count == count_distinct_chars(s@.subrange(0, i as int)),
                seen.dom().finite(),
                forall|c: char| seen.contains_key(c) <==> s@.subrange(0, i as int).contains(c),
            decreases s.len() - i
        {
            if !seen.contains_key(s[i]) {
                seen = seen.insert(s[i], true);
                distinct_count = distinct_count + 1;
            }
            i = i + 1;
        }
        
        (n as i32) - (distinct_count as i32)
    }
}
// </vc-code>


}

fn main() {}