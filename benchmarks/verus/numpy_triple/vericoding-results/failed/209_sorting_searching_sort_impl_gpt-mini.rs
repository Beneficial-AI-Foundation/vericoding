// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): count_concat with proper Seq indexing and ghost proof */
fn count_concat(s1: Seq<i32>, s2: Seq<i32>, x: i32)
    ensures
        count_occurrences(s1 + s2, x) == count_occurrences(s1, x) + count_occurrences(s2, x),
    decreases s1.len()
{
    proof {
        if s1.len() == 0nat {
            // base: empty prefix, s1 + s2 == s2, holds by definition
        } else {
            let _h: i32 = s1@[0int];
            count_concat(s1.skip(1nat), s2, x);
            assert(count_occurrences(s1 + s2, x) == (if s1@[0int] == x { 1int } else { 0int }) + count_occurrences(s1.skip(1nat) + s2, x));
            assert(count_occurrences(s1.skip(1nat) + s2, x) == count_occurrences(s1.skip(1nat), x) + count_occurrences(s2, x));
            assert(count_occurrences(s1 + s2, x) == count_occurrences(s1, x) + count_occurrences(s2, x));
        }
    }
}

/* helper modified by LLM (iteration 5): count_remove using int index and ghost proof */
fn count_remove(seq: Seq<i32>, idx: int, x: i32)
    requires
        0 <= idx,
        idx < seq.len() as int,
    ensures
        count_occurrences(seq.remove(idx), x) == count_occurrences(seq, x) - (if seq@[idx] == x { 1int } else { 0int }),
    decreases seq.len()
{
    proof {
        if idx == 0int {
            assert(count_occurrences(seq, x) == (if seq@[0int] == x { 1int } else { 0int }) + count_occurrences(seq.skip(1nat), x));
            assert(seq.remove(0int) == seq.skip(1nat));
            assert(count_occurrences(seq.remove(0int), x) == count_occurrences(seq.skip(1nat), x));
        } else {
            // recurse on tail
            count_remove(seq.skip(1nat), idx - 1int, x);
            assert(count_occurrences(seq, x) == (if seq@[0int] == x { 1int } else { 0int }) + count_occurrences(seq.skip(1nat), x));
            // characterize remove at idx in terms of head and removal from tail
            assert(seq.remove(idx) == Seq::new(seq.len() - 1nat, |i: int| if i == 0int { seq@[0int] } else { seq.skip(1nat).remove(idx - 1int)@[i - 1int] }));
            assert(count_occurrences(seq.remove(idx), x) == (if seq@[0int] == x { 1int } else { 0int }) + count_occurrences(seq.skip(1nat).remove(idx - 1int), x));
            assert(count_occurrences(seq.skip(1nat).remove(idx - 1int), x) == count_occurrences(seq.skip(1nat), x) - (if seq.skip(1nat)@[idx - 1int] == x { 1int } else { 0int }));
            assert(seq@[idx] == seq.skip(1nat)@[idx - 1int]);
            assert(count_occurrences(seq.remove(idx), x) == count_occurrences(seq, x) - (if seq@[idx] == x { 1int } else { 0int }));
        }
    }
}

/* helper modified by LLM (iteration 5): count_unit for single-element sequence built with Seq::new (ghost proof) */
fn count_unit(m: i32, x: i32)
    ensures
        count_occurrences(Seq::new(1nat, |_: int| m), x) == (if m == x { 1int } else { 0int }),
{
    proof {
        // direct by definition of count_occurrences on length-1 sequence
    }
}

/* helper modified by LLM (iteration 5): find_min_index returns Rust usize for Vec usage (runtime) */
fn find_min_index(v: &Vec<i32>) -> usize
    requires
        v.len() > 0usize,
    ensures
        result < v.len(),
        forall|j: usize| j < v.len() ==> v[result] <= v[j],
    decreases v.len()
{
    let mut i: usize = 0usize;
    let mut min_idx: usize = 0usize;
    while i < v.len()
        invariant
            i <= v.len(),
            min_idx < v.len(),
            forall|j: usize| j < i ==> v[min_idx] <= v[j],
        decreases v.len() - i
    {
        if v[i] < v[min_idx] {
            min_idx = i;
        }
        i = i + 1usize;
    }
    min_idx
}

// </vc-helpers>

// <vc-spec>
spec fn count_occurrences(seq: Seq<i32>, x: i32) -> int
    decreases seq.len()
{
    if seq.len() == 0 {
        0int
    } else {
        (if seq[0] == x { 1int } else { 0int }) + count_occurrences(seq.skip(1), x)
    }
}

fn sort(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        forall|x: i32| count_occurrences(result@, x) == count_occurrences(a@, x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement selection sort with ghost proofs preserving counts */
    let orig_len = a.len();
    let orig_seq = a@;
    let mut a = a;
    let mut res: Vec<i32> = Vec::new();

    while a.len() > 0usize
        invariant
            res.len() + a.len() == orig_len,
            forall|i: int, j: int| 0 <= i < j < res.len() as int ==> res[i as usize] <= res[j as usize],
            forall|x: i32| count_occurrences(res@ + a@, x) == count_occurrences(orig_seq, x),
        decreases a.len()
    {
        let old_res_seq = res@;
        let old_a_seq = a@;
        let idx_usize = find_min_index(&a);
        let m = a.remove(idx_usize);
        res.push(m);
        proof {
            // work in ghost/proof context: convert index to int and show counts preserved
            let idx_int: int = idx_usize as int;

            // use old invariant for old_res_seq + old_a_seq == orig_seq (in counts)
            assert(forall|x: i32| count_occurrences(old_res_seq + old_a_seq, x) == count_occurrences(orig_seq, x));

            // show for arbitrary x that counts of new res + a equal counts of old_res + old_a
            fix x: i32;
            // instantiate lemmas for this x
            count_unit(m, x);
            count_remove(old_a_seq, idx_int, x);
            count_concat(old_res_seq, Seq::new(1nat, |_: int| m), x);
            count_concat(old_res_seq + Seq::new(1nat, |_: int| m), old_a_seq.remove(idx_int), x);

            // combine equalities stepwise
            assert(count_occurrences(res@ + a@, x) == count_occurrences(old_res_seq + Seq::new(1nat, |_: int| m) + old_a_seq.remove(idx_int), x));
            assert(count_occurrences(old_res_seq + Seq::new(1nat, |_: int| m) + old_a_seq.remove(idx_int), x) ==
                   count_occurrences(old_res_seq + Seq::new(1nat, |_: int| m), x) + count_occurrences(old_a_seq.remove(idx_int), x));
            assert(count_occurrences(old_res_seq + Seq::new(1nat, |_: int| m), x) ==
                   count_occurrences(old_res_seq, x) + count_occurrences(Seq::new(1nat, |_: int| m), x));
            assert(count_occurrences(Seq::new(1nat, |_: int| m), x) == (if m == x { 1int } else { 0int }));
            assert(count_occurrences(old_a_seq.remove(idx_int), x) == count_occurrences(old_a_seq, x) - (if old_a_seq@[idx_int] == x { 1int } else { 0int }));

            // combine the arithmetic equalities to conclude counts equal
            assert(count_occurrences(res@ + a@, x) == count_occurrences(old_res_seq, x) + count_occurrences(old_a_seq, x));
            assert(count_occurrences(res@ + a@, x) == count_occurrences(old_res_seq + old_a_seq, x));

            // finally, by old invariant, equal to original sequence counts
            assert(count_occurrences(res@ + a@, x) == count_occurrences(orig_seq, x));
        }
    }

    res
}

// </vc-code>


}
fn main() {}