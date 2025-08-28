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
proof fn lemma_swap_preserves_sorted_before(a: &Vec<(i32, i32)>, old_a: &Vec<(i32, i32)>, j: int, l: int, u: int)
    requires
        j >= 0,
        j + 1 < a.len(),
        a.len() == old_a.len(),
        forall|k: int| 0 <= k < a.len() && k != j && k != j + 1 ==> a[k] == old_a[k],
        a[j] == old_a[j + 1],
        a[j + 1] == old_a[j],
        u < j,
        sorted(old_a, l, u)
    ensures sorted(a, l, u)
{
}

proof fn lemma_swap_preserves_sorted_after(a: &Vec<(i32, i32)>, old_a: &Vec<(i32, i32)>, j: int, l: int, u: int)
    requires
        j >= 0,
        j + 1 < a.len(),
        a.len() == old_a.len(),
        forall|k: int| 0 <= k < a.len() && k != j && k != j + 1 ==> a[k] == old_a[k],
        a[j] == old_a[j + 1],
        a[j + 1] == old_a[j],
        l > j + 1,
        sorted(old_a, l, u)
    ensures sorted(a, l, u)
{
}

proof fn lemma_swap_creates_sorted_region(a: &Vec<(i32, i32)>, old_a: &Vec<(i32, i32)>, j: int)
    requires
        j >= 0,
        j + 1 < a.len(),
        a.len() == old_a.len(),
        forall|k: int| 0 <= k < a.len() && k != j && k != j + 1 ==> a[k] == old_a[k],
        a[j] == old_a[j + 1],
        a[j + 1] == old_a[j],
        old_a[j].1 > old_a[j + 1].1
    ensures sorted(a, j, j + 1)
{
}

proof fn lemma_partitioned_preserved_by_swap(a: &Vec<(i32, i32)>, old_a: &Vec<(i32, i32)>, j: int, i: int)
    requires
        j >= 0,
        j + 1 < a.len(),
        a.len() == old_a.len(),
        forall|k: int| 0 <= k < a.len() && k != j && k != j + 1 ==> a[k] == old_a[k],
        a[j] == old_a[j + 1],
        a[j + 1] == old_a[j],
        partitioned(old_a, i),
        j > i || j + 1 > i
    ensures partitioned(a, i)
{
}

proof fn lemma_sorted_extends_left(a: &Vec<(i32, i32)>, l1: int, l2: int, u: int)
    requires
        l1 <= l2,
        sorted(a, l2, u),
        forall|k: int| l1 <= k < l2 ==> forall|k_prime: int| l2 <= k_prime <= u ==> a[k].1 <= a[k_prime].1
    ensures sorted(a, l1, u)
{
}

proof fn lemma_insertion_creates_partitioned(a: &Vec<(i32, i32)>, i: int)
    requires
        i >= 0,
        i < a.len(),
        sorted(a, 0, i),
        forall|k: int| 0 <= k <= i ==> forall|k_prime: int| i < k_prime < a.len() ==> a[k].1 <= a[k_prime].1
    ensures partitioned(a, i)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn bubble_sort(a: &mut Vec<(i32, i32)>)
    ensures sorted(a, 0, a.len() as int - 1)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let n = a.len();
    if n <= 1 {
        return;
    }
    
    let mut i: usize = 1;
    while i < n
        invariant
            i <= n,
            n == a.len(),
            sorted(a, 0, i as int - 1),
            i == 1 || partitioned(a, i as int - 2)
    {
        let mut j = i;
        while j > 0 && a[j].1 < a[j - 1].1
            invariant
                j <= i,
                i < n,
                n == a.len(),
                sorted(a, 0, j as int - 1),
                sorted(a, j as int + 1, i as int),
                j == i || (a[j].1 <= a[j + 1].1),
                j == 0 || j == i || (forall|k: int| 0 <= k < j ==> a[k].1 <= a[j].1),
                forall|k: int| i < k < a.len() ==> forall|k_prime: int| 0 <= k_prime <= i ==> a[k_prime].1 <= a[k].1
        {
            let temp = a[j];
            a.set(j, a[j - 1]);
            a.set(j - 1, temp);
            j = j - 1;
        }
        
        proof {
            lemma_insertion_creates_partitioned(a, i as int);
        }
        
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}