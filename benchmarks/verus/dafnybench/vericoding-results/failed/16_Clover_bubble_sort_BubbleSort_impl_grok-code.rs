use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::prelude::*;
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<i32>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            #[trigger] forall|k: int, l: int| 0 <= k < l < a@.len() && l < i as int ==> a@[k] <= a@[l],
            #[trigger] forall|k: int| a@.len() - i <= k < a@.len() ==> #[trigger] forall|l: int| k <= l < a@.len() ==> a@[k] <= a@[l],
        decreases a@.len() - i
    {
        let mut j: usize = 0;
        while j < a.len() - i - 1
            invariant
                0 <= i < a@.len(),
                a@.to_multiset() == old(a)@.to_multiset(),
                0 <= j <= a@.len() - i - 1,
                #[trigger] forall|k: int, l: int| 0 <= k < l < a@.len() && l < i as int ==> a@[k] <= a@[l],
                #[trigger] forall|k: int| a@.len() - i <= k < a@.len() ==> #[trigger] forall|l: int| k <= l < a@.len() ==> a@[k] <= a@[l],
            decreases (a@.len() - i - 1) - j
        {
            if a[j] > a[j + 1] {
                let temp = a[j];
                a[j] = a[j + 1];
                a[j + 1] = temp;
            }
            j += 1;
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}