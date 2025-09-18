// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed old() usage with explicit type parameter and immutable reference */
proof fn lemma_vec_len_preserved(a: &Vec<i32>)
    ensures
        a@.len() == old(a)@.len(),
{
}

spec fn is_zero(x: i32) -> bool {
    x == 0
}

spec fn count_nonzero_spec(a: Seq<i32>) -> nat {
    a.filter(|x| x != 0).len()
}

proof fn lemma_count_nonzero_properties(a: Seq<i32>)
    ensures
        count_nonzero_spec(a) <= a.len(),
        a.len() == 0 ==> count_nonzero_spec(a) == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0) ==> count_nonzero_spec(a) == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> count_nonzero_spec(a) == a.len(),
        (exists|i: int| 0 <= i < a.len() && a[i] != 0) ==> count_nonzero_spec(a) > 0,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> count_nonzero_spec(a) < a.len()
{
}

proof fn lemma_vec_len_nonnegative(a: Vec<i32>) 
    ensures 
        a@.len() >= 0,
{
}
// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i32>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed old() usage with explicit type parameter */
{
    let mut count: usize = 0;
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant 
            a@.len() == old::<Vec<i32>>(a)@.len(),
            0 <= idx <= a@.len(),
            count == count_nonzero_spec(a@.subrange(0, idx as int)),
            count <= idx,
    {
        if a[idx] != 0 {
            count = count + 1;
        }
        idx = idx + 1;
    }
    
    count
}
// </vc-code>

}
fn main() {}