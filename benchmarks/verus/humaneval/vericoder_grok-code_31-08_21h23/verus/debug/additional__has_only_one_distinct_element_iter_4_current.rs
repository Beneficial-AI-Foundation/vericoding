use vstd::prelude::*;

verus! {

// <vc-helpers>
//
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if a.len() == 0 {
        return true;
    }
    let mut i: usize = 1;
    while i < a.len()
        invariant(0 <= i as int <= a.len() as int &&
                  forall |k: int| 0 <= k < i as int ==> #[trigger] (a@[k]) == a@[0])
    {
        if a[i] != a[0] {
            proof {
                let witness_i: int = i as int;
                let witness_j: int = 0;
                assert(0 <= witness_i && witness_i < a.len() as int);
                assert(0 <= witness_j && witness_j < a.len() as int);
                assert(a@[witness_i] != a@[witness_j]);
            };
            return false;
        }
        i += 1;
    }
    proof {
        assert(forall |k: int| 0 <= k < a.len() ==> a@[k] == a@[0]);
        assert forall |i: int, j: int| 0 <= i < a.len() as int && 0 <= j < a.len() as int implies a@[i] == a@[j] by {
            assert(a@[i] == a@[0]);
            assert(a@[j] == a@[0]);
        };
    };
    return true;
}
// </vc-code>

fn main() {}
}