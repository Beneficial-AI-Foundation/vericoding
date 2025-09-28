// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Add decreases clause helper and maintain existing helpers */
proof fn lemma_len_nonnegative<T>(v: &Vec<T>)
    ensures
        v@.len() >= 0,
{
}

spec fn contains_spec(seq: Seq<int>, k: int) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == k
}

proof fn lemma_ext_equal<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() == s2.len(),
        forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i],
    ensures
        s1 =~= s2,
{
}
// </vc-helpers>

// <vc-spec>
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)

    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Add decreases clause to while loop */
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i as int <= arr@.len(),
            forall|j: int| 0 <= j < i as int ==> arr@[j] != k,
        decreases arr.len() - i,
    {
        if arr[i] == k {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}