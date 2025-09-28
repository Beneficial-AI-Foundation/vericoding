use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len() / 2
        invariant
            i <= a.len() / 2,
            result.len() == i,
            a.len() % 2 == 0,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == a@[2*j] + a@[2*j + 1],
        decreases
            a.len() / 2 - i,
    {
        // Assert bounds are valid
        assert(2 * i < a.len()) by {
            assert(i < a.len() / 2);
            assert(2 * i < 2 * (a.len() / 2));
            assert(a.len() % 2 == 0);
            assert(2 * (a.len() / 2) == a.len());
        }
        assert(2 * i + 1 < a.len()) by {
            assert(2 * i < a.len());
        }
        
        // Use regular addition (matches specification semantics)
        let sum = a[2*i] + a[2*i + 1];
        result.push(sum);
        
        // Prove the invariant holds after push
        assert(result.len() == i + 1);
        assert(result@.last() == sum);
        
        // Prove that the last element satisfies the specification
        assert(result@[i as int] == a@[2 * i as int] + a@[2 * i as int + 1]) by {
            assert(result@.len() == i + 1);
            assert(result@[i as int] == result@.last());
            assert(result@.last() == sum);
            assert(sum == a[2*i] + a[2*i + 1]);
            assert(a[2*i] + a[2*i + 1] == a@[2 * i as int] + a@[2 * i as int + 1]);
        }
        
        // Prove the forall invariant still holds
        assert forall|j: int| 0 <= j < i + 1 implies #[trigger] result@[j] == a@[2*j] + a@[2*j + 1] by {
            if j < i {
                // Previous elements unchanged by push
                assert(result@[j] == a@[2*j] + a@[2*j + 1]);
            } else {
                // j == i, which we just proved above
                assert(j == i);
                assert(result@[i as int] == a@[2 * i as int] + a@[2 * i as int + 1]);
            }
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}