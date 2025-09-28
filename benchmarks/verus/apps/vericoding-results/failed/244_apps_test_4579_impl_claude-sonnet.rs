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
    /* code modified by LLM (iteration 5): fix contains() type mismatch by cloning string */
    let mut seen = Set::<String>::empty();
    let mut count = 0i8;
    let mut i = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            count as int == seen.len(),
            seen == Set::new(|s: String| exists|j: int| 0 <= j < i && strings@[j] == s),
            count >= 0,
            count as int <= i,
        decreases strings.len() - i
    {
        let current_string = strings[i].clone();
        if !seen.contains(current_string) {
            seen = seen.insert(current_string);
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(seen == Set::new(|s: String| exists|j: int| 0 <= j < strings.len() && strings@[j] == s));
        assert(seen == distinct_strings(strings@));
    }
    
    count
}
// </vc-code>


}

fn main() {}