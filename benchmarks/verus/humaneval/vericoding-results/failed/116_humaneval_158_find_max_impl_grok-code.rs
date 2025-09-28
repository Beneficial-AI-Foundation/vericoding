// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_unique_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix set insert assignment in count_unique */
fn count_unique(s: &String) -> (res: usize)
    ensures 
        res as int == string_unique_chars(s@),
{
    let mut unique = Set::empty();
    for c in s.chars() { 
        unique = unique.insert(c);
    }
    unique.len()
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
/* code modified by LLM (iteration 2): implement find_max by iterating through strings and tracking the one with max unique chars */
{
    let mut max_s = &strings[0];
    let mut max_count = count_unique(max_s);
    for i in 1..strings.len() {
        let current = &strings[i];
        let current_count = count_unique(current);
        if current_count > max_count {
            max_s = current;
            max_count = current_count;
        }
    } 
    max_s.clone()
}
// </vc-code>


}

fn main() {}