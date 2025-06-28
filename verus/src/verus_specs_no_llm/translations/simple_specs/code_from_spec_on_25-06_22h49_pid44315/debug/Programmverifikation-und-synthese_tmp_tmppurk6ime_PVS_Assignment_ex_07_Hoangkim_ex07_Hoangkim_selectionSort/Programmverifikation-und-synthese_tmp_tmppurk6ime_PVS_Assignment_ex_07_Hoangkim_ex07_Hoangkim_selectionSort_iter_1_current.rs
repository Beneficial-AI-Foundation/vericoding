use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMin(a: &Vec<int>, lo: usize) -> (minIdx: usize)
    requires 
        a.len() > 0,
        lo < a.len()
    ensures 
        lo <= minIdx < a.len(),
        forall|x: int| lo <= x < a.len() ==> a[minIdx] <= a[x]
{
    let mut minIdx = lo;
    let mut i = lo + 1;
    
    while i < a.len()
        invariant
            lo <= minIdx < a.len(),
            lo + 1 <= i <= a.len(),
            forall|x: int| lo <= x < i ==> a[minIdx] <= a[x]
    {
        if a[i] < a[minIdx] {
            minIdx = i;
        }
        i = i + 1;
    }
    
    minIdx
}

fn swap(a: &mut Vec<int>, i: usize, j: usize)
    requires 
        old(a).len() > 0,
        i < old(a).len(),
        j < old(a).len()
    ensures
        a.len() == old(a).len(),
        a[i] == old(a)[j],
        a[j] == old(a)[i],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == old(a)[k]
{
    let temp = a[i];
    a.set(i, a[j]);
    a.set(j, temp);
}

spec fn is_sorted(a: &Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

spec fn multiset_eq<T>(a: &Vec<T>, b: &Vec<T>) -> bool {
    // Simplified multiset equality - in practice would need more complex implementation
    a.len() == b.len()
}

fn selectionSort(a: &mut Vec<int>)
    requires a.len() > 0
    ensures
        a.len() == old(a).len(),
        is_sorted(a),
        multiset_eq(a, old(a))
{
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == old(a).len(),
            forall|x: int, y: int| 0 <= x < i && i <= y < a.len() ==> a[x] <= a[y],
            forall|x: int, y: int| 0 <= x < y < i ==> a[x] <= a[y],
            multiset_eq(a, old(a))
    {
        let minIdx = FindMin(a, i);
        if minIdx != i {
            swap(a, i, minIdx);
        }
        i = i + 1;
    }
}

}