use vstd::prelude::*;

verus! {

// <vc-helpers>
fn count_false(a: &Vec<bool>) -> (c: nat)
    ensures c == a@.filter(|v: bool| !v).len(),
{
    let mut count: nat = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            count == a@.subsequence(0, i as nat).filter(|v: bool| !v).len(),
    {
        if !a[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    // pre-conditions-start
    requires
        old(a).len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let len = a.len();
    if len == 0 {
        return;
    }

    let num_false = count_false(a);

    let mut i: usize = 0;
    while i < num_false as usize
        invariant
            i <= num_false as usize,
            num_false <= a.len(),
            a.len() == old(a).len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| 0 <= k < i as int ==> !a[k as usize],
    {
        if a[i] {
            let mut j: usize = num_false as usize;
            proof {
                assert(num_false as int <= len as int);
            }
            while j < len
                invariant
                    num_false as usize <= j <= len,
                    a.len() == old(a).len(),
                    a@.to_multiset() == old(a)@.to_multiset(),
                    forall|k: int| 0 <= k < i as int ==> !a[k as usize],
                    forall|k: int| num_false as int <= k < j as int ==> a[k as usize],
            {
                if !a[j] {
                    a.swap(i, j);
                    break;
                }
                j = j + 1;
            }
        }
        i = i + 1;
    }

    assert(forall|k: int| 0 <= k < num_false as int ==> !a[k as usize]);

    proof {
        assert(a@.to_multiset() == old(a)@.to_multiset());

        let mut false_count_after_sort: nat = 0;
        let mut k: usize = 0;
        while k < len
            invariant
                k <= len,
                false_count_after_sort == a@.subsequence(0, k as nat).filter(|v: bool| !v).len(),
        {
            if !a[k] {
                false_count_after_sort = false_count_after_sort + 1;
            }
            k = k + 1;
        }
        assert(false_count_after_sort == num_false);
        assert(count_false(a) == num_false);

        // Prove that elements from num_false to len-1 are true
        let mut k_true: int = num_false as int;
        while (k_true < len as int)
            invariant
                num_false as int <= k_true <= len as int,
                forall|idx: int| num_false as int <= idx < k_true ==> a[idx as usize],
        {
            assert(a[k_true as usize]); // If this fails, it means there's a false value where there shouldn't be
            k_true = k_true + 1;
        }
        assert(forall|k_final: int| num_false as int <= k_final < len as int ==> a[k_final as usize]);

        assert(forall|i_idx: int, j_idx: int|
                 0 <= i_idx < j_idx < a.len() as int ==> !a[i_idx as usize] || a[j_idx as usize]
        );
    }
    ()
    // impl-end
}
// </vc-code>

fn main() {}
}