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
/* helper modified by LLM (iteration 5): removed requires clause to fix compilation error, adjusted exists bound to handle out-of-bounds */
spec fn distinct_until(strings: Seq<String>, n: int) -> Set<String>
{
    Set::new(|s: String| exists |k: int| 0 <= k < (if n <= strings.len() { n } else { strings.len() }) && strings[k] == s)
}
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
/* code modified by LLM (iteration 5): kept manual implementation unchanged to match postcondition without depending on helper */
{
    let mut count: i8 = 0;
    let mut distinct: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            distinct.len() == count as int,
            distinct@.len() == distinct_until(strings@, i as int).len()
        decreases strings.len() - i
    {
        let s = &strings[i];
        let mut j = 0;
        let mut found = false;
        while j < distinct.len()
            invariant
                j <= distinct.len()
            decreases distinct.len() - j
        {
            if s == &distinct[j] {
                found = true;
                break;
            }
            j += 1;
        }
        if !found {
            distinct.push(s.clone());
            count += 1;
        }
        i += 1;
    }
    (count)
}
// </vc-code>


}

fn main() {}