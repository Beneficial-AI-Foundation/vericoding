use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn mod_lemma(a: int, b: int)
    requires
        b != 0,
    ensures
        a % b == a % b,
{
}

proof fn mod_range_lemma(a: int, b: int)
    requires
        b != 0,
    ensures
        if b > 0 { -b < a % b < b } else { b < a % b < -b },
{
}

spec fn modulo(a: int, b: int) -> int
    recommends
        b != 0,
{
    a % b
}

proof fn vec_index_bound_lemma(vec: &Vec<i32>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        0 <= i < vec@.len(),
{
}

proof fn slice_index_bound_lemma(slice: &[i32], i: int)
    requires
        0 <= i < slice.len(),
    ensures
        0 <= i < slice@.len(),
{
}

proof fn forall_lemma(b: &[i32], i: int)
    requires
        forall|k: int| 0 <= k < b@.len() ==> b@[k] != 0,
        0 <= i < b@.len(),
    ensures
        b@[i] != 0,
{
}

proof fn forall_slice_to_view(b: &[i32])
    requires
        forall|k: int| 0 <= k < b.len() ==> b[k] != 0,
    ensures
        forall|k: int| 0 <= k < b@.len() ==> b@[k] != 0,
{
}
// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    proof {
        forall_slice_to_view(b);
    }
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == modulo(a[j] as int, b[j] as int) as i32,
        decreases a.len() - i,
    {
        proof {
            slice_index_bound_lemma(a, i as int);
            slice_index_bound_lemma(b, i as int);
            forall_lemma(b, i as int);
            assert(b@[i as int] != 0);
        }
        let a_val = a[i];
        let b_val = b[i];
        proof {
            assert(b_val != 0);
            mod_lemma(a_val as int, b_val as int);
            mod_range_lemma(a_val as int, b_val as int);
        }
        let mod_result = a_val % b_val;
        result.push(mod_result);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {
}

}