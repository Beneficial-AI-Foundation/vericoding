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
/* helper modified by LLM (iteration 4): fixed incorrect vstd lemma names to fix compilation */
proof fn proof_to_set_cardinality<T>(s: Seq<T>)
    ensures s.to_set().len() <= s.len()
    decreases s.len()
{
    if s.len() > 0 {
        let t = s.subrange(0, s.len() - 1);
        let last = s.last();
        proof_to_set_cardinality(t);

        assert(s === t.push(last));
        vstd::seq_lib::lemma_seq_to_set_push_is_insert(t, last);

        vstd::set_lib::lemma_cardinality_insert(t.to_set(), last);

        if t.to_set().contains(last) {
            assert(s.to_set() === t.to_set());
            assert(s.to_set().len() == t.to_set().len());
            assert(s.to_set().len() <= t.len());
            assert(s.to_set().len() <= s.len());
        } else {
            assert(s.to_set().len() == t.to_set().len() + 1);
            assert(s.to_set().len() <= t.len() + 1);
            assert(t.len() + 1 == s.len());
            assert(s.to_set().len() <= s.len());
        }
    } else {
        assert(s.to_set().len() == 0 && s.len() == 0);
    }
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
    /* code modified by LLM (iteration 4): fixed incorrect vstd lemma names to fix compilation */
    if n > 26 {
        return -1;
    }

    let mut distinct_chars = Set::<char>::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            s@.len() == n as int,
            n <= 26,
            distinct_chars@ === s@.subrange(0, i as int).to_set(),
    {
        distinct_chars = distinct_chars.insert(s[i]);
        i = i + 1;
    }
    
    proof {
        assert(distinct_chars@ === s@.to_set()) by {
            assert(s@.subrange(0, n as int) === s@) by {
                vstd::seq_lib::lemma_subrange_is_self(s@);
            };
        };

        proof_to_set_cardinality(s@);
        
        assert(valid_input(n as int, s@));
        assert(s@.len() >= 1);
        
        vstd::seq_lib::lemma_mem_of_to_set(s@, 0);
        assert(s@.to_set().contains(s@[0]));
        vstd::set_lib::lemma_cardinality_ge_1_if_contains(s@.to_set(), s@[0]);
    }
    
    let result = (n - distinct_chars.len()) as i32;
    result
}
// </vc-code>


}

fn main() {}