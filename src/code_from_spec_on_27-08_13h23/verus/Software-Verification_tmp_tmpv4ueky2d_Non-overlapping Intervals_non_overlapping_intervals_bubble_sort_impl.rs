use vstd::prelude::*;

verus! {

// Bubble Sort

// Predicates for Bubble Sort
spec fn sorted(a: &Vec<(i32, i32)>, l: int, u: int) -> bool {
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> a[i].1 <= a[j].1
}

spec fn partitioned(a: &Vec<(i32, i32)>, i: int) -> bool {
    forall|k: int, k_prime: int| 0 <= k <= i < k_prime < a.len() ==> a[k].1 <= a[k_prime].1
}

// <vc-helpers>
spec fn is_permutation(a: &Vec<(i32, i32)>, b: &Vec<(i32, i32)>) -> bool {
    a.len() == b.len() &&
    forall|i: int| 0 <= i < a.len() ==> exists|j: int| 0 <= j < b.len() && a[i] == b[j]
}

proof fn lemma_swap_preserves_permutation(a: &Vec<(i32, i32)>, b: &Vec<(i32, i32)>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
        b.len() == a.len(),
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == b[k],
        b[i] == a[j],
        b[j] == a[i],
    ensures
        is_permutation(a, b)
{
    assert forall|i: int| 0 <= i < a.len() implies exists|j: int| 0 <= j < b.len() && a[i] == b[j] by {
        if i == i {
            assert(b[j] == a[i]);
        } else if i == j {
            assert(b[i] == a[j]);
        } else {
            assert(b[i] == a[i]);
        }
    };
}

proof fn lemma_bubble_pass_invariants(a: &Vec<(i32, i32)>, i: int, j: int, max_idx: int)
    requires
        0 <= i <= j < a.len(),
        forall|k: int| 0 <= k < j ==> a[k].1 <= a[k+1].1 || k == max_idx,
    ensures
        partitioned(a, i)
{
    assert forall|k: int, k_prime: int| 0 <= k <= i < k_prime < a.len() implies a[k].1 <= a[k_prime].1 by {
        if k <= i && i < k_prime && k_prime < a.len() {
            assert(a[k].1 <= a[k+1].1 || k == max_idx);
        }
    };
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn bubble_sort(a: &mut Vec<(i32, i32)>)
    ensures sorted(a, 0, a.len() as int - 1)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn bubble_sort(a: &mut Vec<(i32, i32)>)
    ensures
        sorted(a, 0, a.len() as int - 1),
        is_permutation(&old(a), a)
{
    let mut i: int = a.len() as int - 1;
    while i > 0
        invariant
            0 <= i < a.len(),
            sorted(a, i, a.len() as int - 1),
            partitioned(a, i),
            is_permutation(&old(a), a)
    {
        let mut j: int = 0;
        let mut max_idx: int = 0;
        while j < i
            invariant
                0 <= j <= i,
                0 <= max_idx <= j,
                forall|k: int| 0 <= k < j ==> a[k].1 <= a[k+1].1 || k == max_idx,
                sorted(a, i, a.len() as int - 1),
                partitioned(a, i),
                is_permutation(&old(a), a)
        {
            if a[j].1 > a[j+1].1 {
                let tmp = a[j];
                a.set(j, a[j+1]);
                a.set(j+1, tmp);
                max_idx = j;
                proof {
                    lemma_swap_preserves_permutation(&old(a), a, j, j+1);
                }
            }
            j = j + 1;
        }
        proof {
            lemma_bubble_pass_invariants(a, i, j, max_idx);
        }
        i = i - 1;
    }
}
// </vc-code>

fn main() {}

}