// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_unique_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Simplified helper by removing proof block and asserts, which might cause parsing issues.] */
fn count_unique_chars(s: &String) -> (count: usize)
    ensures
        count as int == string_unique_chars(s@),
{
    let mut unique_chars: Set<char> = Set::empty();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            unique_chars == s@.subrange(0, i as int).to_set(),
        decreases s.len() - i
    {
        let current_char = s.get_char(i).unwrap();
        unique_chars = unique_chars.insert(current_char);
        i = i + 1;
    }
    unique_chars.len()
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
/* code modified by LLM (iteration 5): [The implementation logic is sound; failure was likely in the helper. Resubmitting with the corrected helper.] */
{
    let mut max_s = strings[0].clone();
    let mut max_count = count_unique_chars(&max_s);

    let mut i: usize = 1;
    while i < strings.len()
        invariant
            1 <= i <= strings.len(),
            max_count as int == string_unique_chars(max_s@),
            exists|k: int| 0 <= k < i && #[trigger] strings@.index(k)@ == max_s@,
            forall|k: int| 0 <= k < i ==> 
                max_count as int >= string_unique_chars(strings@.index(k)@),
        decreases strings.len() - i
    {
        let current_s = &strings[i];
        let current_count = count_unique_chars(current_s);
        
        if current_count > max_count {
            max_s = current_s.clone();
            max_count = current_count;
        } else {
            // Keep the old max_s to satisfy the postcondition.
        }

        i = i + 1;
    }

    return max_s;
}
// </vc-code>


}

fn main() {}