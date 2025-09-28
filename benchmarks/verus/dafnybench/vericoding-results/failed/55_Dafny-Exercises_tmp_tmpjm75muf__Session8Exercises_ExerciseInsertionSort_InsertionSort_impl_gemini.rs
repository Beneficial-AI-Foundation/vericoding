// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes from previous iteration */
spec fn sorted_seq(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

proof fn lemma_insert_preserves_sorted(prefix: Seq<i32>, key: i32, ip: int)
    requires
        sorted_seq(prefix),
        0 <= ip <= prefix.len() as int,
        ip == 0 || prefix[ip - 1] <= key,
        ip == prefix.len() as int || key <= prefix[ip],
    ensures
        sorted_seq(prefix.subrange(0, ip).push(key) + prefix.subrange(ip, prefix.len() as int)),
{
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    ensures 
        sorted_seg(a, 0, (a.len() - 1) as int),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using a temporary variable for swap */
    let n = a.len();
    if n <= 1 {
        return;
    }

    let mut i: usize = 1;
    while i < n
        invariant
            1 <= (i as int) && (i as int) <= (n as int),
            sorted_seg(a, 0, (i - 1) as int),
            a@.to_multiset() == old(a)@.to_multiset(),
        decreases n - i
    {
        let key = a[i];
        let ghost a_before_inner = a@;

        let mut j = i;
        while j > 0 && a[j-1] > key
            invariant
                0 < j && j <= i,
                (i as int) < (n as int),
                a@.to_multiset() == a_before_inner.to_multiset(),
                a@.subrange((i + 1) as int, n as int) == a_before_inner.subrange((i + 1) as int, n as int),
                sorted_seg(a, 0, (j - 1) as int),
                forall|k: int| (j as int) < k && k <= (i as int) ==> a@[k] > key,
                sorted_seg(a, (j + 1) as int, i as int),
                a@[j as int] == key,
            decreases j
        {
            let prev_j = j - 1;
            a.swap(prev_j, j);
            j = j - 1;
        }

        i += 1;
    }
}
// </vc-code>

}
fn main() {}