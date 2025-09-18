// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): general sequence/vector membership predicates used in specs */
spec fn contains_in_seq<T>(s: Seq<T>, x: T) -> bool {
    exists|j: int| 0 <= j && j < s.len() && s[j] == x
}

spec fn contains_in_vec<T>(v: &Vec<T>, x: T) -> bool {
    contains_in_seq::<T>(v@, x)
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
    /* code modified by LLM (iteration 4): implement in1d with nested loops and proper loop invariants */
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < ar1.len()
        invariant
            i <= ar1.len(),
            res.len() == i,
            forall|k: int| 0 <= k && k < i as int ==> res@[k] == (exists|j: int| 0 <= j && j < ar2.len() as int && ar1@[k] == ar2@[j])
        decreases ar1.len() as int - i as int
    {
        let mut j: usize = 0;
        let mut found: bool = false;
        while j < ar2.len()
            invariant
                j <= ar2.len(),
                i < ar1.len(),
                found == (exists|k: int| 0 <= k && k < j as int && ar2@[k] == ar1@[i as int])
            decreases ar2.len() as int - j as int
        {
            if ar2[j] == ar1[i] {
                found = true;
            }
            j = j + 1;
        }
        proof {
            assert(j == ar2.len());
            assert(found == (exists|k: int| 0 <= k && k < ar2.len() as int && ar2@[k] == ar1@[i as int]));
        }
        res.push(found);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}