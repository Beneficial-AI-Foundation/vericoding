use vstd::prelude::*;

verus! {

// flips (i.e., reverses) array elements in the range [0..num]

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn flip(a: &mut Vec<i32>, num: usize)
    requires 
        old(a).len() > 0,
        num < old(a).len(),
    ensures
        forall|k: int| 0 <= k <= num as int ==> #[trigger] a[k] == old(a)[num as int - k],
        // forall k :: num < k < a.Length ==> a[k] == old(a[k])
        a.len() == old(a).len(),
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    while i <= num / 2
        invariant
            a.len() == old(a).len(),
            num < old(a).len(),
            i <= num / 2 + 1,
            forall|k: int| 0 <= k < i ==> #[trigger] a[k] == old(a)[num as int - k],
            forall|k: int| num as int - i < k <= num as int ==> #[trigger] a[k] == old(a)[num as int - k],
            forall|k: int| i <= k <= num as int - i ==> #[trigger] a[k] == old(a)[k],
        decreases num / 2 + 1 - i
    {
        let temp = a[i];
        let temp2 = a[num - i];
        a.set(i, temp2);
        a.set(num - i, temp);
        i += 1;
    }
}
// </vc-code>

fn main() {}

}