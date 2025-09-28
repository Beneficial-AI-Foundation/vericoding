// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_unique_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove non-negativity of unique char count */
fn unique_chars_nonneg(s: Seq<char>)
    ensures
        string_unique_chars(s) >= 0,
{
    proof {
        assert(s.to_set().len() as int >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn find_max(strings: Vec<String>) -> (s: String)
    requires 
        strings.len() > 0,
    ensures 
        exists|i: int| 0 <= i < strings.len() && #[trigger] strings@.index(i)@  s@,
        forall|i: int| 0 <= i < strings.len() ==> 
            string_unique_chars(s@) >= #[trigger] string_unique_chars(#[trigger] strings@.index(i)@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): find string with maximum unique characters */
    let n = strings.len();
    let mut best: usize = 0usize;
    let mut j: usize = 1usize;
    while j < n
        invariant
            0 <= (best as int) && (best as int) < n as int,
            forall|k: int| 0 <= k < (j as int) ==> string_unique_chars(strings@.index(best as int)@) >= string_unique_chars(strings@.index(k)@),
        decreases (n as int) - (j as int)
    {
        if string_unique_chars(strings@.index(j as int)@) > string_unique_chars(strings@.index(best as int)@) {
            best = j;
        }
        j = j + 1usize;
    }
    strings[best].clone()
}
// </vc-code>


}

fn main() {}