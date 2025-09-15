// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper needed from previous iteration to fix current errors. */
// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type issues, especially for array indexing and `nat` arithmetic. */
{
    let mut seen_count: nat = 0; 
    let mut i: int = 0;

    while i < a.len() as int
        invariant
            0 <= i <= a.len() as int,
            seen_count == count_occurrences(a@.subsequence(0, i as nat), key),
    {
        if a[i as usize] == key {
            seen_count = seen_count + 1; 
        }
        i = i + 1;
    }
    
    (seen_count == 1)
}
// </vc-code>

}
fn main() {}