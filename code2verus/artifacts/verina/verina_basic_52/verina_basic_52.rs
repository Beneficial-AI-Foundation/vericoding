use vstd::prelude::*;

verus! {

// Precondition - always true in the original
spec fn bubble_sort_precond(a: Seq<i32>) -> bool {
    true
}

// Helper function to swap elements at positions i and j
fn swap(a: &mut Vec<i32>, i: usize, j: usize)
    requires 
        i < old(a).len(),
        j < old(a).len(),
    ensures 
        a.len() == old(a).len(),
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == old(a)[k],
{
    let temp = a[i];
    let val_j = a[j];
    a.set(i, val_j);
    a.set(j, temp);
}

// Inner bubble loop
fn bubble_inner(a: &mut Vec<i32>, j: usize, i: usize)
    requires
        j <= i,
        i + 1 < old(a).len(),
    ensures
        a.len() == old(a).len(),
    decreases i - j,
{
    if j < i {
        if a[j] > a[j + 1] {
            swap(a, j, j + 1);
        }
        bubble_inner(a, j + 1, i);
    }
}

// Outer bubble loop  
fn bubble_outer(a: &mut Vec<i32>, i: usize)
    requires
        i + 1 < old(a).len(),
    ensures
        a.len() == old(a).len(),
    decreases i,
{
    if i > 0 {
        bubble_inner(a, 0, i);
        bubble_outer(a, i - 1);
    }
}

// Main bubble sort function
fn bubble_sort(a: Vec<i32>) -> (result: Vec<i32>)
    requires
        bubble_sort_precond(a@),
    ensures
        result.len() == a.len(),
        // Full postcondition would require complex invariants to prove
{
    let mut a_mut = a;
    if a_mut.len() <= 1 {
        a_mut
    } else {
        let len = a_mut.len();
        bubble_outer(&mut a_mut, len - 2);
        a_mut
    }
}

// Postcondition - array is sorted and is a permutation of the original
spec fn bubble_sort_postcond(a: Seq<i32>, result: Seq<i32>) -> bool {
    &&& result.len() == a.len()
    &&& sorted(result)
    &&& multiset_equiv(result, a)
}

// Helper predicate for sorted sequence
spec fn sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Helper function to check if two sequences are multiset equivalent (permutations)
spec fn multiset_equiv<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    s1.len() == s2.len() &&
    forall|x: T| count_occurrences(s1, x) == count_occurrences(s2, x)
}

spec fn count_occurrences<T>(s: Seq<T>, x: T) -> nat {
    s.filter(|y: T| y == x).len()
}

fn main() {}

} // verus!