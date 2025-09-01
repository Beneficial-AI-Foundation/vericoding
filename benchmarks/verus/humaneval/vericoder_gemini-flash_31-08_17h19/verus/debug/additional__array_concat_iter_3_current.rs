use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::loop_isolation(false)]
proof fn lemma_concat_len_plus_one(start_len: nat, x: i32)
    ensures
        Vec::<i32>::new().push(x).len() == 1,
        (Vec::<i32>::new().set_len_unchecked(start_len as int)).push(x).len() == start_len + 1,
{}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> result[i + a.len()] == b[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();

    let mut i: nat = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[j],
    {
        result.push(a.get(i as usize).unwrap());
        i = i + 1;
    }

    let mut k: nat = 0;
    while k < b.len()
        invariant
            k <= b.len(),
            result.len() == a.len() + k,
            forall|j: int| 0 <= j && j < a.len() ==> result[j] == a[j],
            forall|j: int| 0 <= j && j < k ==> result[j + a.len()] == b[j],
    {
        result.push(b.get(k as usize).unwrap());
        k = k + 1;
    }
    result
}
// </vc-code>

fn main() {}
}