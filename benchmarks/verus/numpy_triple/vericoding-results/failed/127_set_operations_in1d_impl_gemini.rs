// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn spec_contains<T: PartialEq>(s: Seq<T>, elem: T) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == elem
}

/* helper modified by LLM (iteration 5): [Corrected path for exists_intro to vstd::seq_lib] */
fn vec_contains<T: PartialEq>(v: &Vec<T>, elem: &T) -> (result: bool)
    ensures result == spec_contains(v.view(), *elem)
{
    let s = v.view();
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            !spec_contains(s.subrange(0, i as int), *elem)
    {
        if v[i] == *elem {
            proof {
                vstd::seq_lib::exists_intro(s, |j: int| s[j] == *elem, i as int);
            }
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-helpers>

// <vc-spec>
fn in1d<T: PartialEq>(ar1: Vec<T>, ar2: Vec<T>) -> (result: Vec<bool>)
    ensures 
        result.len() == ar1.len(),
        forall|i: int| 0 <= i < ar1.len() ==> 
            result[i] == exists|j: int| 0 <= j < ar2.len() && ar1[i] == ar2[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [No functional change; logic should verify after helper fix] */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < ar1.len()
        invariant
            0 <= i <= ar1.len(),
            result.len() == i,
            forall|k: int| 0 <= k < (i as int) ==> 
                result.view()[k] == (exists|j: int| 0 <= j < ar2.len() && ar1.view()[k] == ar2.view()[j])
    {
        let present = vec_contains(&ar2, &ar1[i]);
        result.push(present);
        proof {
            let k = i as int;
            let elem = ar1.view()[k];
            assert(result.view()[k] == present);
            assert(present == spec_contains(ar2.view(), elem));
            assert(spec_contains(ar2.view(), elem) == (exists|j: int| 0 <= j < ar2.len() && elem == ar2.view()[j]));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}