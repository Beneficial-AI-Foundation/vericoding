use vstd::prelude::*;

verus! {

spec fn triple(a: &[int]) -> bool {
    exists|i: int| 0 <= i < a.len() - 2 && #[trigger] a[i] == a[i + 1] && a[i + 1] == a[i + 2]
}

// <vc-helpers>
proof fn triple_exists_witness(a: &[int], i: int)
    requires 
        0 <= i < a.len() - 2,
        a[i] == a[i + 1] && a[i + 1] == a[i + 2]
    ensures triple(a)
{
}

proof fn triple_not_exists(a: &[int])
    requires 
        forall|i: int| 0 <= i < a.len() - 2 ==> !(#[trigger] a[i] == a[i + 1] && a[i + 1] == a[i + 2])
    ensures !triple(a)
{
}
// </vc-helpers>

// <vc-spec>
fn get_triple(a: &[int]) -> (index: usize)
ensures 
    (0 <= index < a.len() - 1) || index == a.len(),
    index == a.len() <==> !triple(a),
    (0 <= index < a.len() - 1) <==> triple(a),
    (0 <= index < a.len() - 1) ==> a[index as int] == a[index as int + 1] && a[index as int + 1] == a[index as int + 2]
// </vc-spec>
// <vc-code>
{
    if a.len() < 3 {
        proof {
            assert forall|i: int| 0 <= i < a.len() - 2 implies !(#[trigger] a[i] == a[i + 1] && a[i + 1] == a[i + 2]) by {
                assert(a.len() - 2 <= 0);
            };
            triple_not_exists(a);
        }
        return a.len();
    }

    let mut index = 0;
    while index < a.len() - 2
        invariant
            0 <= index <= a.len() - 2,
            forall|i: int| 0 <= i < index ==> !(#[trigger] a[i] == a[i + 1] && a[i + 1] == a[i + 2])
        decreases a.len() - 2 - index
    {
        if a[index] == a[index + 1] && a[index + 1] == a[index + 2] {
            proof {
                triple_exists_witness(a, index as int);
            }
            return index;
        }
        index += 1;
    }

    proof {
        assert forall|i: int| 0 <= i < a.len() - 2 implies !(#[trigger] a[i] == a[i + 1] && a[i + 1] == a[i + 2]) by {};
        triple_not_exists(a);
    }
    a.len()
}
// </vc-code>

fn main() {}

}