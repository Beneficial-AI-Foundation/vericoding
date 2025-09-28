use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<i32>, i: int, j: int) -> bool //j excluded
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn sorted_seg(a: Seq<i32>, i: int, j: int) -> bool //j excluded
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

proof fn bubble_sort_helper(
    a: Seq<i32>,
    c: int,
    f: int,
)
    requires
        0 <= c <= f <= a.len(),
        f - c <= 1,
    ensures
        sorted_seg(a, c, f),
{
    if f - c == 0 {
        reveal_with_fuel(sorted_seg, 2);
    } else {
        reveal_with_fuel(sorted_seg, 2);
    }
}

proof fn swap_proof(
    old_a: Seq<i32>,
    new_a: Seq<i32>,
    i: int,
    j: int,
)
    requires
        0 <= i < old_a.len(),
        0 <= j < old_a.len(),
        new_a == old_a.update(i, old_a[j]).update(j, old_a[i]),
    ensures
        new_a.to_multiset() == old_a.to_multiset(),
{
}

ghost fn swap_indices(seq: Seq<i32>, i: int, j: int) -> (output: Seq<i32>)
    requires
        0 <= i < seq.len(),
        0 <= j < seq.len(),
    ensures
        output == seq.update(i, seq[j]).update(j, seq[i]),
        output.len() == seq.len(),
        output.to_multiset() == seq.to_multiset(),
{
    seq.update(i, seq[j]).update(j, seq[i])
}
// </vc-helpers>

// <vc-spec>
fn bubbleSorta(a: &mut Vec<i32>, c: usize, f: usize) //f excluded
    requires 
        c <= f,
        f <= old(a).len(), //when c==f empty sequence
    ensures 
        sorted_seg(a@, c as int, f as int),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
// </vc-spec>
// <vc-code>
{
    let mut n = f;
    let mut swapped = true;
    
    while swapped
        invariant
            c <= n <= f,
            n <= f,
            sorted_seg(a@, n as int, f as int),
            a@.subrange(n as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            forall|i: int, j: int|
                n <= i < j < f ==> a@[i] <= a@[j],
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
    {
        if n == c {
            swapped = false;
        } else {
            swapped = false;
            let mut i = c;
            
            while i < n - 1
                invariant
                    c <= i < n,
                    swapped ==> 
                        exists|k: int| c <= k < i && a@[k] > a@[k + 1],
                    !swapped ==> 
                        forall|k: int| c <= k < i ==> a@[k] <= a@[k + 1],
                    a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                    a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
                    a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                    forall|k: int| i < k < n ==> a@[k] <= a@[k + 1],
            {
                if a[i] > a[i + 1] {
                    a.swap(i, i + 1);
                    swapped = true;
                    
                    proof {
                        let old_a = a@;
                        let new_a = swap_indices(old_a, i as int, (i + 1) as int);
                        assert(a@ == new_a);
                        swap_proof(old_a, new_a, i as int, (i + 1) as int);
                    }
                }
                i = i + 1;
            }
            
            n = n - 1;
        }
    }
}
// </vc-code>

fn main() {}

}