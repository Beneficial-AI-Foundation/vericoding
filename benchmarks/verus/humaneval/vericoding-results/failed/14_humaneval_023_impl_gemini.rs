// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    true
}

spec fn correct_length(s: Seq<char>) -> int {
    s.len() as int
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn strlen(s: &str) -> (result: usize)
    requires valid_input(s@)
    ensures correct_length(s@) == (result as int)
{
    assume(false);
    unreached()
}
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [used correct lemmas for invariant and post-condition] */
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.is_char_boundary(i),
            count as nat == s.subslice(0, i)@.len(),
        decreases s.len() - i
    {
        let next_i = vstd::unicode::next_char_boundary(s, i);
        proof {
            vstd::string::lemma_subslice_subslice_view(s, 0, i, next_i);
            vstd::unicode::lemma_next_char_is_one_char(s, i);
        }
        i = next_i;
        count = count + 1;
    }

    proof {
        vstd::string::lemma_subslice_total(s);
    }

    count
}
// </vc-code>


}

fn main() {}