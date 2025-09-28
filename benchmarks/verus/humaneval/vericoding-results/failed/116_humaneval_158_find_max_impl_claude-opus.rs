// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_unique_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Implement find_max to return string with most unique chars */
    let mut max_string = strings[0].clone();
    let mut max_unique = string_unique_chars(max_string@);
    let mut i: usize = 1;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            exists|j: int| 0 <= j < i && strings@.index(j)@ == max_string@,
            forall|j: int| 0 <= j < i ==> string_unique_chars(max_string@) >= string_unique_chars(strings@.index(j)@),
            max_unique == string_unique_chars(max_string@),
    {
        let current_unique = string_unique_chars(strings[i]@);
        if current_unique > max_unique {
            max_string = strings[i].clone();
            max_unique = current_unique;
        }
        i = i + 1;
    }
    
    max_string
}
// </vc-code>


}

fn main() {}