use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace(arr: &mut Vec<i32>, k: i32)
    ensures 
        forall|i: int| 0 <= i < old(arr).len() ==> old(arr)[i] > k ==> arr[i] == -1,
        forall|i: int| 0 <= i < old(arr).len() ==> old(arr)[i] <= k ==> arr[i] == old(arr)[i],
// </vc-spec>
// <vc-code>
{
    let n = arr.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            i as int <= n as int,
            arr.len() == n,
            n as int == old(arr).len(),
            forall|j: int| 0 <= j && j < i as int ==> (
                if old(arr)[j] > k { arr[j] == -1 } else { arr[j] == old(arr)[j] }
            ),
            forall|j: int| i as int <= j && j < n as int ==> arr[j] == old(arr)[j]
        decreases n as int - i as int
    {
        let x = arr[i];
        assert(x == old(arr)[i as int]);
        if x > k {
            arr.set(i, -1);
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}

}