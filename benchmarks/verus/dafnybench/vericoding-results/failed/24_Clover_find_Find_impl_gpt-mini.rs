use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn find(a: &[i32], key: i32) -> (index: i32)
    ensures
        -1 <= index < a.len() as i32,
        index != -1 ==> a[index as int] == key && (forall|i: int| 0 <= i < index ==> a[i] != key),
        index == -1 ==> (forall|i: int| 0 <= i < a.len() ==> a[i] != key),
// </vc-spec>
// <vc-code>
{
    let n: nat = a.len();
    let mut i: nat = 0;
    while i < n
        invariant i <= n;
        invariant forall|k: nat| k < i ==> a[k as usize] != key;
        decreases n - i;
    {
        if a[i as usize] == key {
            proof {
                assert(a[i as usize] == key);
                assert(forall|k: nat| k < i ==> a[k as usize] != key);
            }
            return i as i32;
        }
        i += 1;
    }
    proof {
        // From loop exit we have !(i < n) => i >= n, together with invariant i <= n gives i == n.
        assert(!(i < n));
        assert(i <= n);
        assert(i == n);
        assert(forall|k: nat| k < i ==> a[k as usize] != key);
    }
    return -1;
}
// </vc-code>

fn main() {}

}