// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn multiset_count<T>(s: Seq<T>, x: T) -> nat {
    s.filter(|y| y == x).len()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by using usize for loop indices instead of int */
    let mut v = a;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i as int <= v.len() as int,
            forall|k: int, l: int| 0 <= k < l <= i as int ==> v@[k] as int <= v@[l] as int,
            forall|x: i8| multiset_count(v@, x) == multiset_count(a@, x),
        decreases
            v.len() as int - i as int
    {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < v.len()
            invariant
                i <= min_idx <= v.len(),
                i + 1 <= j <= v.len(),
                forall|x: i8| multiset_count(v@, x) == multiset_count(a@, x),
                forall|m: int| i as int <= m < j as int ==> v@[min_idx] as int <= v@[m] as int,
            decreases
                v.len() as int - j as int
        {
            if v[j] < v[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        if i != min_idx {
            v.swap(i, min_idx);
        }
        i += 1;
    }
    v
}
// </vc-code>


}
fn main() {}