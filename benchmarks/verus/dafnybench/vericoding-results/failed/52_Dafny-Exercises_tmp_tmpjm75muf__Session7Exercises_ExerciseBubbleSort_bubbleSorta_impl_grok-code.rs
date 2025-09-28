use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<i32>, i: int, j: int) -> bool //j excluded
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
// </vc-helpers>
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
    proof { }
    let length = f - c;
    if length <= 1 { return; }
    let start = c;
    let mut i: usize = 0;
    while i < length - 1
        decreases length as int - i as int;
        invariant
            old(a)@.subrange(0, c as int) == a@.subrange(0, c as int),
            old(a)@.subrange(f as int, old(a).len() as int) == a@.subrange(f as int, a.len() as int),
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            sorted_seg(a@, f as int - (i + 1), f as int),
    {
        let mut j: usize = 0;
        while j < length - 1 - i
            decreases length as int - 1 - i as int - j as int;
            invariant
                old(a)@.subrange(0, c as int) == a@.subrange(0, c as int),
                old(a)@.subrange(f as int, old(a).len() as int) == a@.subrange(f as int, a.len() as int),
                a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                sorted_seg(a@, f as int - (i + 1), f as int),
        {
            let idx = start + j;
            let idx1 = idx + 1;
            if a[idx] > a[idx1] {
                let temp = a[idx];
                a[idx] = a[idx1];
                a[idx1] = temp;
            }
            j = j + 1;
        }
        proof {
            assert(sorted_seg(a@, f as int - (i + 1), f as int));
        }
        i = i + 1;
    }
    proof {
        assert(sorted_seg(a@, f as int - length as int, f as int));
    }
}
// </vc-code>

fn main() {}

}