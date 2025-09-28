use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn swap_preserves_multiset<T>(s1: Seq<T>, s2: Seq<T>, i: int, j: int) -> bool {
    s1.len() == s2.len() &&
    0 <= i < s1.len() &&
    0 <= j < s1.len() &&
    s1[i] == s2[j] &&
    s1[j] == s2[i] &&
    (forall|k: int| 0 <= k < s1.len() && k != i && k != j ==> s1[k] == s2[k])
}

proof fn swap_multiset_lemma<T>(s1: Seq<T>, s2: Seq<T>, i: int, j: int)
    requires swap_preserves_multiset(s1, s2, i, j)
    ensures s1.to_multiset() == s2.to_multiset()
{
    if i == j {
        assert(s1 =~= s2);
    } else {
        let s_mid = s1.update(i, s1[j]);
        let s_final = s_mid.update(j, s1[i]);
        
        assert(s_final.len() == s1.len());
        assert(forall|k: int| 0 <= k < s1.len() ==> {
            if k == i {
                s_final[k] == s1[j] && s_final[k] == s2[k]
            } else if k == j {
                s_final[k] == s1[i] && s_final[k] == s2[k]
            } else {
                s_final[k] == s1[k] && s_final[k] == s2[k]
            }
        });
        assert(s_final =~= s2);
    }
}

proof fn sorted_seg_extends(a: Seq<int>, i: int, j: int, k: int)
    requires 
        0 <= i <= j <= k <= a.len(),
        sorted_seg(a, i, j),
        sorted_seg(a, j, k),
        j < k ==> (forall|l: int| i <= l < j ==> a[l] <= a[j])
    ensures sorted_seg(a, i, k)
{
}

proof fn bubble_step_maintains_sorted(a_old: Seq<int>, a_new: Seq<int>, i: usize, j: usize, c: usize)
    requires
        c <= i < j < a_old.len(),
        a_old[i as int] > a_old[j as int],
        swap_preserves_multiset(a_old, a_new, i as int, j as int),
        sorted_seg(a_old, c as int, i as int + 1),
        forall|k: int| i as int + 1 <= k < j && k < a_old.len() ==> a_old[i as int] <= a_old[k]
    ensures
        sorted_seg(a_new, c as int, i as int + 1),
        forall|k: int| i as int + 1 <= k <= j && k < a_new.len() ==> a_new[i as int] <= a_new[k]
{
}

proof fn multiset_preservation_after_swap<T>(a_old: Seq<T>, a_new: Seq<T>, i: usize, j: usize, c: usize, f: usize, orig: Seq<T>)
    requires
        c <= i < j < f <= a_old.len(),
        swap_preserves_multiset(a_old, a_new, i as int, j as int),
        a_old.subrange(c as int, f as int).to_multiset() == orig.subrange(c as int, f as int).to_multiset(),
        a_old.len() == orig.len()
    ensures
        a_new.subrange(c as int, f as int).to_multiset() == orig.subrange(c as int, f as int).to_multiset()
{
    swap_multiset_lemma(a_old, a_new, i as int, j as int);
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<int>, c: usize, f: usize)
    requires 
        0 <= c <= f <= old(a).len(),
    ensures 
        sorted_seg(a@, c as int, f as int),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int),
// </vc-spec>
// <vc-code>
{
    let ghost orig_a = a@;
    let mut i = c;
    while i < f
        invariant
            c <= i <= f,
            i <= a.len(),
            f <= a.len(),
            a.len() == orig_a.len(),
            sorted_seg(a@, c as int, i as int),
            a@.subrange(c as int, f as int).to_multiset() == orig_a.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == orig_a.subrange(0, c as int),
            a@.subrange(f as int, a@.len() as int) == orig_a.subrange(f as int, orig_a.len() as int),
        decreases f - i
    {
        let mut j = i + 1;
        let ghost loop_start_a = a@;
        while j < f
            invariant
                c <= i < j <= f,
                i < a.len(),
                j <= a.len(),
                f <= a.len(),
                a.len() == orig_a.len(),
                sorted_seg(a@, c as int, i as int + 1),
                forall|k: int| i as int + 1 <= k < j && k < a.len() ==> a@[i as int] <= a@[k],
                a@.subrange(c as int, f as int).to_multiset() == orig_a.subrange(c as int, f as int).to_multiset(),
                a@.subrange(0, c as int) == orig_a.subrange(0, c as int),
                a@.subrange(f as int, a@.len() as int) == orig_a.subrange(f as int, orig_a.len() as int),
            decreases f - j
        {
            if a[i] > a[j] {
                proof {
                    let old_seq = a@;
                    assert(swap_preserves_multiset(old_seq, old_seq.update(i as int, old_seq[j as int]).update(j as int, old_seq[i as int]), i as int, j as int));
                    multiset_preservation_after_swap(old_seq, old_seq.update(i as int, old_seq[j as int]).update(j as int, old_seq[i as int]), i, j, c, f, orig_a);
                    bubble_step_maintains_sorted(old_seq, old_seq.update(i as int, old_seq[j as int]).update(j as int, old_seq[i as int]), i, j, c);
                }
                let temp_i = a[i];
                let temp_j = a[j];
                a.set(i, temp_j);
                a.set(j, temp_i);
            }
            j += 1;
        }
        
        proof {
            if i + 1 < f {
                assert(sorted_seg(a@, c as int, i as int + 1));
                assert(forall|k: int| i as int + 1 <= k < f && k < a.len() ==> a@[i as int] <= a@[k]);
                sorted_seg_extends(a@, c as int, i as int + 1, i as int + 2);
            }
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}