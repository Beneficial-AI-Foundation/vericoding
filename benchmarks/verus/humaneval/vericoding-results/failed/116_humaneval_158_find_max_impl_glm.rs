// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_unique_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed while loop invariant formatting */
fn string_unique_chars_exec(s: &String) -> int {
    let seq = s.view();
    let mut set = Set::empty();
    let mut i = 0;
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            set == seq.subrange(0, i).to_set(),
        decreases seq.len() - i
    {
        set = set.insert(seq[i]);
        i += 1;
    }
    set.len() as int
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
    /* code modified by LLM (iteration 2): fixed while loop invariant formatting */
    let mut max_index = 0;
    let mut max_count = string_unique_chars_exec(&strings[0]);
    let mut i = 1;
    while i < strings.len()
        invariant
            1 <= i <= strings.len(),
            0 <= max_index < i,
            string_unique_chars(strings@[max_index]@) == max_count,
            forall|j: int| 0 <= j < i ==> string_unique_chars(strings@[j]@) <= max_count,
        decreases strings.len() - i
    {
        let current_count = string_unique_chars_exec(&strings[i]);
        if current_count > max_count {
            max_count = current_count;
            max_index = i;
        }
        i += 1;
    }
    strings[max_index].clone()
}
// </vc-code>


}

fn main() {}