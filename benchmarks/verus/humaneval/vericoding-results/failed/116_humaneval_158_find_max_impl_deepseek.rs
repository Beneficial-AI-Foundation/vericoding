// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_unique_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_unique_chars_str_eq(a: String, b: String)
    ensures
        a@ == b@ ==> string_unique_chars(a@) == string_unique_chars(b@),
{
}

spec fn spec_strings_len_ge_0(strings: Vec<String>) -> bool {
    strings.len() > 0
}

spec fn spec_sequence_equals(s1: Seq<char>, s2: Seq<char>) -> bool {
    s1 == s2
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
    /* code modified by LLM (iteration 5): Fixed sequence equality syntax in ensures clause */
    let mut max_index = 0;
    let mut max_chars = string_unique_chars(strings[0]@);
    
    let mut i: usize = 1;
    while i < strings.len()
        invariant
            0 <= max_index < strings.len(),
            max_chars == string_unique_chars(strings[max_index]@),
            forall|j: int| 0 <= j < i ==> string_unique_chars(strings[max_index]@) >= string_unique_chars(strings[j]@),
        decreases strings.len() - i,
    {
        let current_chars = string_unique_chars(strings[i]@);
        if current_chars > max_chars {
            max_index = i;
            max_chars = current_chars;
        }
        i += 1;
    }
    
    strings[max_index].clone()
}
// </vc-code>


}

fn main() {}