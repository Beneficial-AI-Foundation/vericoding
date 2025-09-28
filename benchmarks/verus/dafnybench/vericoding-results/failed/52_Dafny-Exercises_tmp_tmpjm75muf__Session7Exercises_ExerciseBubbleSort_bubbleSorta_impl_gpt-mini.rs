use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<i32>, i: int, j: int) -> bool //j excluded
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
// Helper sequence swap
spec fn seq_swap(s: Seq<i32>, i: int, j: int) -> Seq<i32>
    requires 0 <= i && i < s.len() && 0 <= j && j < s.len()
{
    s.set(i, s[j]).set(j, s[i])
}

proof fn seq_swap_preserves_multiset(s: Seq<i32>, i: int, j: int)
    requires 0 <= i && i < s.len() && 0 <= j && j < s.len()
    ensures seq_swap(s,i,j).to_multiset() == s.to_multiset()
{
    if i == j {
        assert(seq_swap(s,i,j) == s);
    } else {
        assert(forall|v: i32| seq_swap(s,i,j).to_multiset().count(v) == s.to_multiset().count(v));
    }
    assert(seq_swap(s,i,j).to_multiset() == s.to_multiset());
}

proof fn subrange_swap_preserves_multiset(s: Seq<i32>, i: int, j: int, c: int, f: int)
    requires 0 <= c && c <= f && f <= s.len()
    requires c <= i && i < f && c <= j && j < f
    ensures seq_swap(s,i,j).subrange(c,f).to_multiset() == s.subrange(c,f).to_multiset()
{
    let sr = s.subrange(c,f);
    let ii = i - c;
    let jj = j - c;
    // indices ii and jj are valid for sr
    assert(0 <= ii && ii < sr.len());
    assert(0 <= jj && jj < sr.len());
    // show elementwise equality between the two representations on the subrange
    assert(forall|k: int| 0 <= k && k < (f - c) ==>
        seq_swap(s,i,j).subrange(c,f)[k] == seq_swap(sr, ii, jj)[k]
    );
    // apply seq_swap_preserves_multiset to the subrange sr
    seq_swap_preserves_multiset(sr, ii, jj);
    assert(seq_swap(sr, ii, jj).to_multiset() == sr.to_multiset());
    // conclude equality of multisets for the subrange
    assert(seq_swap(s,i,j).subrange(c,f).to_multiset() == sr.to_multiset());
    assert(seq_swap(s,i,j).subrange(c,f).to_multiset() == s.subrange(c,f).to_multiset());
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
    // Save original sequence for verification (snapshot of current a)
    let a0: Seq<i32> = a@;

    // If empty segment or single element, nothing to do.
    if c + 1 >= f {
        return;
    }

    // Selection sort on segment [c, f)
    let mut i: usize = c;
    while i < f {
        invariant
            c <= i && i <= f,
            f <= a.len(),
            a@.subrange(0, c as int) == a0.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == a0.subrange(f as int, a0.len() as int),
            a@.subrange(c as int, f as int).to_multiset() == a0.subrange(c as int, f as int).to_multiset(),
            // prefix [c, i) is sorted
            (forall|x: int, y: int| c as int <= x && x < y && y < i as int ==> a@[x as usize] <= a@[y as usize]),
            // every element in prefix [c, i) is <= every element in suffix [i, f)
            (forall|x: int, y: int| c as int <= x && x < i as int && i as int <= y && y < f as int ==>
                a@[x as usize] <= a@[y as usize]
            )
        ;
        {
            // find index m of minimum element in [i, f)
            let mut m: usize = i;
            let mut j: usize = i + 1;
            while j < f {
                invariant
                    i <= m && m < f,
                    i + 1 <= j && j <= f,
                    f <= a.len(),
                    a@.subrange(0, c as int) == a0.subrange(0, c as int),
                    a@.subrange(f as int, a.len() as int) == a0.subrange(f as int, a0.len() as int),
                    a@.subrange(c as int, f as int).to_multiset() == a0.subrange(c as int, f as int).to_multiset(),
                    // m is index of minimum in [i, j)
                    (forall|k: int| i as int <= k && k < j as int ==> a@[m as usize] <= a@[k as usize]),
                    // prefix invariants unchanged
                    (forall|x: int, y: int| c as int <= x && x < y && y < i as int ==> a@[x as usize] <= a@[y as usize]),
                    (forall|x: int, y: int| c as int <= x && x < i as int && i as int <= y && y < f as int ==>
                        a@[x as usize] <= a@[y as usize]
                    )
                ;
                {
                    if a@[j] < a@[m] {
                        m
// </vc-code>

fn main() {}

}