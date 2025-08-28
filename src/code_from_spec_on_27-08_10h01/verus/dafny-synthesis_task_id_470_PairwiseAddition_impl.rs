use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn seq_index_safe(s: Seq<i32>, i: int) -> i32
{
    s[i]
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn pairwise_addition(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() % 2 == 0,
    ensures
        result.len() == a.len() / 2,
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == a[2*i] + a[2*i + 1],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i % 2 == 0,
            i <= a.len(),
            result.len() == i / 2,
            forall|j: int| 0 <= j < result.len() ==> result[j as int] == a@[2*j] + a@[2*j + 1],
        decreases a.len() - i
    {
        proof {
            assert(i < a.len());
            assert(i % 2 == 0);
            assert(a.len() % 2 == 0);
            assert(i + 1 < a.len()) by {
                assert(a.len() - i >= 2);
            };
            assert(0 <= i < a.len());
            assert(0 <= i + 1 < a.len());
        }
        result.push(a[i] + a[i + 1]);
        i += 2;
    }
    
    result
}
// </vc-code>

fn main() {}

}