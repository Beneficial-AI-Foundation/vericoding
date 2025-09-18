// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unreachable */
// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type of `i` and added assertion to guarantee length */
    let mut count: nat = 0nat;
    let mut i: int = 0;

    while i < a.len() as int
        invariant
            0 <= i,
            (i as nat) <= a.len(),
            count == count_occurrences(a@.subsequence(0, i as nat ), key),
        decreases a.len() as int - i
    {
        // assert that a[i] is valid
        assert(0 <= i && (i as nat) < a.len());
        // The `as int` and `as nat` casts are necessary for ghost/spec variables
        if a[i as usize] == key {
            count = count + 1;
        }
        i = i + 1;
    }
    count == 1nat
}
// </vc-code>

}
fn main() {}