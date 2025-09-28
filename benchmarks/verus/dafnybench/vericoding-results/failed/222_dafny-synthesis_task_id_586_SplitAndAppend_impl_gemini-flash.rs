use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::arithmetic::int_traits::DivEuclidian;

#[verus::trusted]
fn mod_len(x: int, len: int) -> (r: int)
    requires len > 0,
    ensures 0 <= r < len,
{
    x.div_euclidian(len)
}
// </vc-helpers>

// <vc-spec>
fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<int> = Vec::new();
    let original_len = l.len();

    // Prove that original_len is positive since n < original_len and n >= 0
    assert(original_len > 0);

    for i in 0..original_len
        invariant
            result.len() == i,
            0 <= i <= original_len,
            forall|j: int| 0 <= j < i ==> result.view()[j] == l[mod_len(j as int + n, original_len as int)],
    {
        // Convert `i` to `int` within the proof block or when assigning to a ghost variable
        proof {
            let i_int: int = i as int; // Convert loop variable to 'int' for calculations
            let offset_idx_val = (i_int + n);
            let wrapped_idx = mod_len(offset_idx_val, original_len as int);
            let val_to_push = l[wrapped_idx];
            result.push(val_to_push);
        }
    }

    // Prove the postcondition
    assert(result.len() == original_len);
    assert(forall|i: int| 0 <= i < original_len ==> result.view()[i] == l[mod_len(i as int + n, original_len as int)]);
    result.view()
}
// </vc-code>

fn main() {
}

}