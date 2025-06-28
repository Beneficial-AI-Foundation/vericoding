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
        forall|x: usize| lo <= x < a.len() ==> a[minIdx as int] <= a[x as int]
{
    let mut minIdx = lo;
    let mut i = lo + 1;
    
    while i < a.len()
        invariant
            lo <= minIdx < a.len(),
            lo + 1 <= i <= a.len(),
            forall|x: usize| lo <= x < i ==> a[minIdx as int] <= a[x as int]
    {
        if a[i as int] < a[minIdx as int] {
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
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|k: usize| 0 <= k < a.len() && k != i && k != j ==> a[k as int] == old(a)[k as int]
{
    let temp = a[i as int];
    a.set(i as int, a[j as int]);
    a.set(j as int, temp);
}

spec fn is_sorted(a: &Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

spec fn multiset_eq<T>(a: &Vec<T>, b: &Vec<T>) -> bool {
    a.len() == b.len() &&
    forall|i: int| 0 <= i < a.len() ==> 
        count_occurrences(a, a[i]) == count_occurrences(b, a[i])
}

spec fn count_occurrences<T>(a: &Vec<T>, val: T) -> nat {
    if a.len() == 0 {
        0
    } else {
        count_occurrences(&a.subrange(0, a.len() - 1), val) + 
        if a[a.len() - 1] == val { 1 } else { 0 }
    }
}

fn selectionSort(a: &mut Vec<int>)
    requires a.len() > 0
    ensures
        a.len() == old(a).len(),
        is_sorted(a),
        multiset_eq(a, old(a))
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == old(a).len(),
            forall|x: int, y: int| 0 <= x < i && i as int <= y < a.len() ==> a[x] <= a[y],
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