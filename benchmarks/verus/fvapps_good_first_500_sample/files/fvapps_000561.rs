// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power2::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_valid_subsequences(words: Vec<Seq<char>>) -> (result: Vec<nat>)
    ensures
        result.len() == words.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < words.len() ==>
            (forall|j: int| 0 <= j < words[i].len() ==> words[i][j] != 'a') ==>
            result[i] == 0,
        forall|i: int| 0 <= i < words.len() ==>
            (forall|j: int| 0 <= j < words[i].len() ==> words[i][j] == 'a') ==>
            result[i] == (pow2(words[i].len()) - 1),
        forall|i: int| 0 <= i < words.len() ==>
            result[i] < pow2(words[i].len())
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}