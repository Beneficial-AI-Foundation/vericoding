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
fn reverse_upto_k(s: &mut Vec<i32>, k: usize)
    requires 
        2 <= k,
        k <= old(s).len(),
    ensures 
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < k ==> array_index(s@, i) == array_index(old(s)@, k - 1 - i),
        forall|i: int| k <= i < s.len() ==> array_index(s@, i) == array_index(old(s)@, i),
{
    let mut i: usize = 0;
    while i < k / 2
        invariant
            k <= s.len(),
            s.len() == old(s).len(),
            forall|j: int| 0 <= j < i ==> array_index(s@, j) == array_index(old(s)@, k - 1 - j),
            forall|j: int| i <= j < k - i ==> array_index(s@, j) == array_index(old(s)@, j),
            forall|j: int| k - i <= j < k ==> array_index(s@, j) == array_index(old(s)@, k - 1 - j),
            forall|j: int| k <= j < s.len() ==> array_index(s@, j) == array_index(old(s)@, j),
    {
        let temp = s[i];
        s.set(i, s[k - 1 - i]);
        s.set(k - 1 - i, temp);
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}