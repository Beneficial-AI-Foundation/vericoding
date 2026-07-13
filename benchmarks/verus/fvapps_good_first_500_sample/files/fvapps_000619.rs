// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn MOD() -> nat { 1000000007 }

fn count_substring_appearances(n: usize, strings: Vec<Vec<char>>) -> (result: Vec<usize>)
    ensures 
        result.len() == strings.len(),
        forall|i: int| 0 <= i < strings.len() ==> {
            if strings[i].len() > n {
                result[i] == 0
            } else {
                result[i] < MOD()
            }
        },
        strings.len() == 0 ==> result.len() == 0,
        (n == 1 && strings.len() == 1 && strings[0].len() == 1) ==> result[0] == 1,
        (n == 1 && strings.len() == 1 && strings[0].len() > 1) ==> result[0] == 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible

    // Test cases:
    // count_substring_appearances(2, vec![vec!['a', 'a']]) should return [1]
    // count_substring_appearances(2, vec![vec!['d']]) should return [52] 
    // count_substring_appearances(12, vec![vec!['c','d','m','n'], vec!['q','w','e','e','w','e','f'], vec!['q','s']]) should return [443568031, 71288256, 41317270]
}