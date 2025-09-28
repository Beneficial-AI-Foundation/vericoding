use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] <= a[k]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], value: int) -> (index: i32)
    requires 
        sorted(a),
    ensures 
        0 <= index ==> index < a.len() && a[index as int] == value,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != value,
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] a[k] != value,
            sorted(a)
    {
        if a[i] == value {
            return i as i32;
        }
        i = i + 1;
    }
    assert(i == a.len());
    assert forall |k: int| 0 <= k < a.len() implies #[trigger] a[k] != value by {
        if 0 <= k && k < a.len() {
            assert(0 <= k && k < i);
            assert(a[k] != value);
        }
    };
    -1
}
// </vc-code>

fn main() {
}

}