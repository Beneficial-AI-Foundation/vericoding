use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn array_index(v: Seq<i32>, i: int) -> i32 {
    v[i]
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn reverse_upto_k(s: &mut Vec<i32>, k: usize)
    requires 
        2 <= k,
        k <= old(s).len(),
    ensures 
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < k ==> array_index(s@, i) == array_index(old(s)@, k - 1 - i),
        forall|i: int| k <= i < s.len() ==> array_index(s@, i) == array_index(old(s)@, i),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut left = 0;
    let mut right = k - 1;
    
    while left < right
        invariant
            0 <= left,
            right < k,
            k <= s.len(),
            s.len() == old(s).len(),
            forall|i: int| 0 <= i < left ==> #[trigger] array_index(s@, i) == array_index(old(s)@, k - 1 - i),
            forall|i: int| right < i < k ==> #[trigger] array_index(s@, i) == array_index(old(s)@, k - 1 - i),
            forall|i: int| left <= i <= right ==> #[trigger] array_index(s@, left + right - i) == array_index(old(s)@, i),
            forall|i: int| left <= i <= right ==> #[trigger] array_index(s@, i) == array_index(old(s)@, left + right - i),
            forall|i: int| k <= i < s.len() ==> #[trigger] array_index(s@, i) == array_index(old(s)@, i),
        decreases right - left
    {
        let temp = s[left];
        let right_val = s[right];
        s.set(left, right_val);
        s.set(right, temp);
        left += 1;
        right -= 1;
    }
}
// </vc-code>

fn main() {
}

}