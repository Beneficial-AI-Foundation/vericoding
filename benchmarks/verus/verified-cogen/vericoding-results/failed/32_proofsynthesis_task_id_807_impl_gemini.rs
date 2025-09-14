// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn check_find_first_odd(arr: &Vec<u32>, index: Option<usize>) -> (result: bool)
{
    if let Some(idx) = index {
        &&& arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
        &&& arr[idx as int] % 2 != 0
    } else {
        forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed incorrect stdlib function call */
proof fn lemma_prefix_is_even(s: Seq<u32>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] % 2 == 0,
    ensures
        s == s.filter(|x: u32| x % 2 == 0),
{
    let p = |x: u32| x % 2 == 0;
    assert forall |x: u32| s.contains(x) implies p(x) by {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
        assert(p(s[i]));
    };
    vstd::seq::lemma_forall_to_matches(s, p);
}
// </vc-helpers>

// <vc-spec>
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)

    ensures check_find_first_odd(arr, index),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): wrapped ghost code in proof block */
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < (i as int) ==> arr[k] % 2 == 0,
        decreases arr.len() - i
    {
        if arr[i] % 2 != 0 {
            proof {
                lemma_prefix_is_even(arr@.take(i as int));
            }
            return Some(i);
        }
        i = i + 1;
    }
    None
}
// </vc-code>

}
fn main() {}