use vstd::prelude::*;

verus! {

spec fn triple(a: &[int]) -> bool {
    exists|i: int| 0 <= i < a.len() - 2 && #[trigger] a[i] == a[i + 1] && a[i + 1] == a[i + 2]
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn get_triple(a: &[int]) -> (index: usize)
ensures 
    (0 <= index < a.len() - 1) || index == a.len(),
    index == a.len() <==> !triple(a),
    (0 <= index < a.len() - 1) <==> triple(a),
    (0 <= index < a.len() - 1) ==> a[index as int] == a[index as int + 1] && a[index as int + 1] == a[index as int + 2]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i - 2 ==> !(a[j] == a[j + 1] && a[j + 1] == a[j + 2])
    {
        if i + 2 < a.len() && a[i as int] == a[i as int + 1] && a[i as int + 1] == a[i as int + 2] {
            proof {
                assert(exists|k: int| 0 <= k < a.len() - 2 && #[trigger] a[k] == a[k + 1] && a[k + 1] == a[k + 2]) by {
                    assert(0 <= i as int && i as int < a.len() - 2 && a[i as int] == a[i as int + 1] && a[i as int + 1] == a[i as int + 2]);
                }
            }
            return i;
        }
        i = i + 1;
    }
    proof {
        assert(!triple(a)) by {
            if exists|k: int| 0 <= k < a.len() - 2 && #[trigger] a[k] == a[k + 1] && a[k + 1] == a[k + 2] {
                let k = choose|k: int| 0 <= k < a.len() - 2 && a[k] == a[k + 1] && a[k + 1] == a[k + 2];
                assert(0 <= k < i as int - 2);
                assert(false);
            }
        }
    }
    a.len()
}
// </vc-code>

fn main() {}

}