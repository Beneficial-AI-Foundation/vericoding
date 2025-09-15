// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn list_to_nat(l: Seq<u32>) -> nat
    decreases l.len(),
{
    if l.len() == 0 {
        0nat
    } else {
        l[0] as nat + 10nat * list_to_nat(l.subrange(1, l.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add new_vec_with helper */
fn new_vec_with<T: Copy>(len: int, val: T) -> Vec<T> {
    let mut vec = Vec::new();
    vec.reserve(len);
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            vec.len() == i,
            vec.capacity() >= len,
            vec@.len() == i,
    {
        vec.push(val);
        i = i + 1;
    }
    vec
}
// </vc-helpers>

// <vc-spec>
fn add_two_numbers(l1: &Vec<u32>, l2: &Vec<u32>) -> (result: Vec<u32>)
    requires 
        l1.len() > 0,
        l2.len() > 0,
        forall|i: int| 0 <= i < l1.len() ==> l1[i] < 10,
        forall|i: int| 0 <= i < l2.len() ==> l2[i] < 10,
        (l1[l1.len() - 1] != 0 || l1@ == seq![0u32]) &&
        (l2[l2.len() - 1] != 0 || l2@ == seq![0u32]),
    ensures
        list_to_nat(result@) == list_to_nat(l1@) + list_to_nat(l2@),
        forall|i: int| 0 <= i < result.len() ==> result[i] < 10,
        result[result.len() - 1] != 0 || (l1@ == seq![0u32] && l2@ == seq![0u32] && result@ == seq![0u32]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): call new_vec_with directly */
{
    let n1 = list_to_nat(l1@);
    let n2 = list_to_nat(l2@);
    let sum = n1 + n2;

    lemma_list_to_nat_nat_to_list(sum);
    lemma_nat_to_list_always_valid(sum);

    let result_seq = nat_to_list(sum);

    let mut result_vec = Vec::new();
    result_vec.reserve(result_seq.len() as usize);

    let mut i = 0;
    while i < result_seq.len()
        invariant
            0 <= i <= result_seq.len(),
            result_vec.len() == i,
            result_vec.capacity() >= result_seq.len(),
            result_vec@.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec@[j] == result_seq@[j],
    {
        result_vec.push(result_seq.index(i));
        i = i + 1;
    }

    result_vec
}
// </vc-code>

}
fn main() {}