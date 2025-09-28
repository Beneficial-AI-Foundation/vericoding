use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn pairwise_addition(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() % 2 == 0,
    ensures
        result.len() == a.len() / 2,
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == a[2*i] + a[2*i + 1],
// </vc-spec>
// <vc-code>
{
    let len_a = a.len() / 2;
    let mut result = Vec::<i32>::new();

    #[verifier::loop_isolation(false)]
    for i in 0..len_a
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result@[j] == a@[2 * j] + a@[2 * j + 1],
    {
        let pair = a[2 * i].wrapping_add(a[2 * i + 1]);
        result.push(pair);
        proof {
            assert (result@[i] == a@[2 * i] + a@[2 * i + 1]);
        }
    }

    result
}
// </vc-code>

fn main() {}

}