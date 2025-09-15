// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_min_index(a: &Vec<i32>, start: usize) -> (result: usize)
    requires start < a.len()
    ensures start <= result < a.len(),
            forall|i: int| start <= i < a.len() ==> a[result as int] <= a[i]
{
    let mut min_idx = start;
    let mut i = start + 1;
    while i < a.len()
        invariant
            start <= min_idx < a.len(),
            start + 1 <= i <= a.len(),
            forall|j: int| start <= j < i ==> a[min_idx as int] <= a[j]
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    min_idx
}

fn swap(a: &mut Vec<i32>, i: usize, j: usize)
    requires i < old(a).len(), j < old(a).len()
    ensures a.len() == old(a).len(),
            a[i as int] == old(a)[j as int],
            a[j as int] == old(a)[i as int],
            forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == old(a)[k]
{
    let temp = a[i];
    a.set(i, a[j]);
    a.set(j, temp);
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
        result@ =~= a@,
// </vc-spec>
// <vc-code>
{
    let mut result = a.clone();
    let mut i = 0;
    
    while i < result.len()
        invariant
            0 <= i <= result.len(),
            result.len() == a.len(),
            result@ =~= a@,
            forall|x: int, y: int| 0 <= x <= y < i ==> result[x] <= result[y]
    {
        if i + 1 < result.len() {
            let min_idx = find_min_index(&result, i);
            if min_idx != i {
                swap(&mut result, i, min_idx);
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}