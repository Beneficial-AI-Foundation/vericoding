use vstd::prelude::*;

verus! {

// Two-state predicate for checking if multiset is preserved
spec fn preserved(a_old: Seq<i32>, a_new: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a_old.len() && a_old.len() == a_new.len()
{
    a_old.subrange(left as int, right as int).to_multiset() == a_new.subrange(left as int, right as int).to_multiset()
}

// Predicate for checking if array slice is ordered
spec fn ordered(a: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a.len()
{
    forall|i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// Two-state predicate for sorted array
spec fn sorted(a_old: Seq<i32>, a_new: Seq<i32>) -> bool
    recommends a_old.len() == a_new.len()
{
    ordered(a_new, 0, a_new.len() as nat) && preserved(a_old, a_new, 0, a_old.len() as nat)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(old(a)@, a@)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len()
            && preserved(old(a)@, a@, 0, (a@.len() as nat))
            && ordered(a@, 0, (i as nat))
            && forall |k: int, m: int| 0 <= k < (i as nat) && (i as nat) <= m < (a@.len() as nat) ==> #[trigger] (a@[k]) <= a@[m]
        decreases a.len() - i
    {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < a.len()
            invariant 
                i <= j <= a.len()
                && i <= min_idx < j
                && preserved(old(a)@, a@, 0, (a@.len() as nat))
                && forall |k: int| i <= k < (j as nat) ==> #[trigger] (a@[k]) >= a@[min_idx as int]
            decreases a.len() - j
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        // swap a[i] and a[min_idx]
        let temp = a[i];
        a[i] = a[min_idx];
        a[min_idx] = temp;
        proof {
            assert(forall |p: int| 0 <= p < (i as nat) ==> #[trigger] (a@[p]) <= a@[i as int]);
            assert(ordered(a@, 0, ((i + 1) as nat)));
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}