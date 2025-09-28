// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn multiset_count<T>(s: Seq<T>, x: T) -> nat {
    s.filter(|y| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed requires clause to use old(a) for mutable reference */
fn min(a: i8, b: i8) -> (result: i8)
    ensures
        result <= a,
        result <= b,
        result == a || result == b,
{
    if a < b { a } else { b }
}

fn insertion_sort_inner(a: &mut Vec<i8>, start: usize, end: usize)
    requires
        0 <= start <= end <= old(a).len(),
        forall|i: int, j: int| 0 <= i < j < start as int ==> old(a)[i] as int <= old(a)[j] as int,
        forall|x: i8| multiset_count(old(a)@.subrange(0, start as int), x) == multiset_count(old(a)@.subrange(0, start as int), x),
    ensures
        forall|i: int, j: int| 0 <= i < j < end as int ==> a[i] as int <= a[j] as int,
        forall|x: i8| multiset_count(a@.subrange(0, end as int), x) == multiset_count(old(a)@.subrange(0, end as int), x),
{
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            forall|k: int, l: int| 0 <= k < l < i as int ==> a[k] as int <= a[l] as int,
            forall|x: i8| multiset_count(a@.subrange(0, i as int), x) == multiset_count(old(a)@.subrange(0, i as int), x),
        decreases end - i
    {
        let mut j = i;
        while j > 0 && a[j-1] > a[j]
            invariant
                0 <= j <= i,
                forall|k: int, l: int| 
                    0 <= k < l < i as int && !(k == j-1 && l == j) ==> a[k] as int <= a[l] as int,
                forall|x: i8| multiset_count(a@.subrange(0, i as int), x) == multiset_count(old(a)@.subrange(0, i as int), x),
            decreases j
        {
            let prev = j - 1;
            let temp = a[j];
            a[j] = a[prev];
            a[prev] = temp;
            j = prev;
        }
        i = i + 1;
    }
}
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
    /* code modified by LLM (iteration 4): fixed complex argument in swap call */
    let mut a = a;
    insertion_sort_inner(&mut a, 0, a.len());
    a
}
// </vc-code>


}
fn main() {}