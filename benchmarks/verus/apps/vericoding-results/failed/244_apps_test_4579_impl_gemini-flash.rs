// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn distinct_strings(strings: Seq<String>) -> Set<String> {
    Set::new(|s: String| exists|i: int| 0 <= i < strings.len() && strings[i] == s)
}

spec fn valid_input(strings: Seq<String>) -> bool {
    strings.len() >= 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(strings: Vec<String>) -> (count: i8)
    requires 
        valid_input(strings@)
    ensures 
        count as int >= 1,
        count as int <= strings@.len(),
        count as int == distinct_strings(strings@).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed a compilation issue with Set::<String>::empty(). */
    let mut distinct_count: i8 = 0;
    let mut seen_strings: Set<String> = Set::empty();

    let mut i: usize = 0;
    while i < strings.len()
        invariant
            0 <= i,
            i <= strings.len(),
            distinct_count as int == seen_strings.len(),
            forall|s: String| seen_strings.contains(s) ==
                exists|j: int| 0 <= j < i as int && strings@[j] == s,
            forall|s: String| seen_strings.contains(s) ==> distinct_strings(strings@).contains(s),
            distinct_count as int >= 0,
            distinct_count as int <= i as int,
        decreases strings.len() - i
    {
        let current_string: &String = &strings[i];
        if !seen_strings.contains(current_string.clone()) {
            seen_strings = seen_strings.insert(current_string.clone());
            distinct_count = (distinct_count + 1) as i8;
        }
        i = i + 1;
    }
    distinct_count
}
// </vc-code>


}

fn main() {}