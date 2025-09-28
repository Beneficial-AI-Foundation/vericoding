use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn sorted(s: Seq<i32>, low: int, high: int) -> bool {
    forall|i: int, j: int| low <= i < j < high ==> s[i] <= s[j]
}

spec fn perm(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}

proof fn lemma_swap_preserves_multiset(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        a.update(i, a[j]).update(j, a[i]).to_multiset() == a.to_multiset()
{
}

proof fn lemma_sorted_prefix_suffix(a: Seq<i32>, i: int, len: int)
    requires
        0 <= i <= len <= a.len(),
        sorted(a, 0, len),
    ensures
        sorted(a, 0, i) && sorted(a, i, len)
{
}

proof fn lemma_merge_sorted(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len() - 1,
        sorted(a, 0, i),
        sorted(a, i, a.len()),
        a[i] <= a[i + 1],
    ensures
        sorted(a, 0, a.len())
{
}

proof fn lemma_bubble_pass_preserves_multiset(a: Seq<i32>, len: int) -> (b: Seq<i32>)
    requires
        0 <= len <= a.len(),
    ensures
        b == a,
        perm(b, a)
{
    a
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<i32>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len() as int;
    let mut i: int = 0;
    while i < n
        invariant
            i <= n,
            forall|k: int, l: int| 0 <= k < l < (n - i) ==> a@[k] <= a@[l],
            sorted(a@, n - i, n),
            perm(a@, old(a)@),
    {
        let mut j: int = 0;
        while j < n - i - 1
            invariant
                j <= n - i - 1,
                forall|k: int| 0 <= k < j ==> a@[k] <= a@[k + 1],
                sorted(a@, n - i, n),
                perm(a@, old(a)@),
        {
            if a[j as usize] > a[(j + 1) as usize] {
                proof {
                    lemma_swap_preserves_multiset(a@, j, j + 1);
                }
                let temp = a[j as usize];
                a[j as usize] = a[(j + 1) as usize];
                a[(j + 1) as usize] = temp;
            }
            j = j + 1;
        }
        proof {
            lemma_sorted_prefix_suffix(a@, n - i - 1, n);
            if i < n - 1 {
                lemma_merge_sorted(a@, n - i - 1);
            }
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}