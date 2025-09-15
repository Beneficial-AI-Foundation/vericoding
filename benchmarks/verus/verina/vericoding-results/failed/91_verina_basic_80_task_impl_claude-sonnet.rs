// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed nat suffixes from expressions */
proof fn lemma_subrange_full(a: Seq<i32>)
    ensures a.subrange(0, a.len() as int) =~= a
{
}

proof fn lemma_subrange_extend(a: Seq<i32>, i: int, key: i32)
    requires 0 <= i < a.len()
    ensures count_occurrences(a.subrange(0, i + 1), key) == 
            count_occurrences(a.subrange(0, i), key) + (if a[i] == key { 1 } else { 0 })
{
}
// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed nat suffixes from numeric literals */
    let mut count: nat = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == count_occurrences(a@.subrange(0, i as int), key),
            count <= i
        decreases a.len() - i
    {
        if a[i] == key {
            proof {
                lemma_subrange_extend(a@, i as int, key);
            }
            count = count + 1;
        } else {
            proof {
                lemma_subrange_extend(a@, i as int, key);
            }
        }
        i = i + 1;
    }
    proof {
        lemma_subrange_full(a@);
    }
    count == 1
}
// </vc-code>

}
fn main() {}