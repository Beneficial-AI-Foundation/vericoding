// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn swap_seq<T>(s: Seq<T>, i: int, j: int) -> Seq<T>
    recommends 0 <= i < s.len() && 0 <= j < s.len()
{
    if i == j { s } else { s.update(i, s[j]).update(j, s[i]) }
}

proof fn lemma_swap_seq_props<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len()
    ensures
        swap_seq(s, i, j)[i] == s[j],
        swap_seq(s, i, j)[j] == s[i],
        forall|k: int| 0 <= k < s.len() && k != i && k != j ==> swap_seq(s, i, j)[k] == s[k]
{
}

// </vc-helpers>

// <vc-spec>
fn swap(arr: &Vec<i32>, i: usize, j: usize) -> (result: Vec<i32>)
    requires
        i < arr.len(),
        j < arr.len(),
    ensures
        result.len() == arr.len(),
        result[i as int] == arr[j as int],
        result[j as int] == arr[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> result[k] == arr[k],
// </vc-spec>
// <vc-code>
{
    let mut r = arr.clone();
    if i != j {
        let vi = r[i];
        let vj = r[j];
        r.set(i, vj);
        r.set(j, vi);
    }
    r
}
// </vc-code>

}
fn main() {}