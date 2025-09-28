// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_seq_filter_len_properties(a: Seq<i32>, key: i32) 
    ensures
        count_occurrences(a, key) == a.filter(|x: i32| x == key).len(),
{
    reveal(count_occurrences);
    /* helper modified by LLM (iteration 5): Removed redundant proof body */
}
// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Removed lemma call to fix compilation error */
    let mut count: u64 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            count == count_occurrences(a@.subrange(0, i as int), key),
            0 <= i && i <= a.len(),
            count <= a.len() as u64,
        decreases a.len() - i,
    {
        if a[i] == key {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count == 1
}
// </vc-code>

}
fn main() {}