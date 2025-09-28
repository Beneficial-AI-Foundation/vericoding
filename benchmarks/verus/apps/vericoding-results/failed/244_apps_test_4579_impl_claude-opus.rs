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
    /* code modified by LLM (iteration 5): Remove clone() call and use ghost reference directly */
    let ghost mut seen = Set::<String>::empty();
    let mut count: i8 = 0;
    let mut i: usize = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            0 <= count <= i,
            count >= 0,
            count as int <= strings@.len(),
            seen == distinct_strings(strings@.subrange(0, i as int)),
            count as int == seen.len()
    {
        // Check if we've seen this string before
        let mut found = false;
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i,
                found == exists|k: int| 0 <= k < j && strings@[k] == strings@[i as int]
        {
            if strings[j] == strings[i] {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if !found {
            proof {
                let ghost current_str = strings@[i as int];
                seen = seen.insert(current_str);
            }
            count = count + 1;
        }
        i = i + 1;
    }
    
    assert(strings@.subrange(0, strings@.len() as int) == strings@);
    assert(seen == distinct_strings(strings@));
    assert(count as int == distinct_strings(strings@).len());
    assert(distinct_strings(strings@).len() >= 1) by {
        assert(strings@.len() >= 1);
        assert(0 <= 0 < strings@.len());
        assert(strings@[0] == strings@[0]);
        assert(distinct_strings(strings@).contains(strings@[0]));
    }
    
    count
}
// </vc-code>


}

fn main() {}