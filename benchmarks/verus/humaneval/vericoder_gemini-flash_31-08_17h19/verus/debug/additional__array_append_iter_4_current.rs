use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::loop_isolation(false)]
fn array_append_spec(a: Vec<i32>, b: i32) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + 1,
        forall|i: int| #![auto] 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
{
    let mut result = Vec::new();
    let old_a_len = a.len();

    // Copy elements from 'a'
    let mut i: int = 0;
    while i < old_a_len
        invariant
            0 <= i <= old_a_len,
            result.len() == i,
            forall|j: int| #![trigger result[j]] 0 <= j && j < i ==> result[j] == a[j],
    {
        result.push(a[i as usize]);
        i = i + 1;
    }

    // Append 'b'
    result.push(b);

    result
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_append(a: Vec<i32>, b: i32) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + 1,
        forall|i: int| #![auto] 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let old_a_len = a.len();

    let mut i: int = 0;
    while i < old_a_len
        invariant
            0 <= i <= old_a_len,
            result.len() == i,
            forall|j: int| #![trigger result[j]] 0 <= j && j < i ==> result[j] == a[j],
    {
        result.push(a[i as usize]);
        i = i + 1;
    }

    result.push(b);

    proof {
        assert(result.len() == old_a_len + 1);
        assert(result.len() == (a.len() as int) + 1); // a.len() is old_a_len

        forall |k: int| #[trigger result[k]]
            0 <= k && k < result.len() implies result[k] == (if k < old_a_len { a[k] } else { b })
        {
            if k < old_a_len {
                assert(result[k] == a[k]);
            } else {
                assert(k == old_a_len);
                assert(result[k] == b);
            }
        }
    }

    result
}
// </vc-code>

fn main() {}
}