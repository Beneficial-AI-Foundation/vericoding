// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use nat literals with nat suffix for all nat operations */
    let mut count: nat = 0nat;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == count_occurrences(a@.subrange(0, i as int), key),
        decreases a.len() - i
    {
        if a[i] == key {
            count = count + 1nat;
        }
        i = i + 1;
    }
    proof {
        assert(a@.subrange(0, a.len() as int) =~= a@);
    }
    count == 1nat
}
// </vc-code>

}
fn main() {}