// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): refactored to use more general IFF-style lemmas */
spec fn count_nonzero_spec(s: Seq<i32>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        count_nonzero_spec(s.drop_last()) + if s.last() != 0 { 1nat } else { 0nat }
    }
}

proof fn lemma_count_le_len(s: Seq<i32>)
    ensures count_nonzero_spec(s) <= s.len()
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_le_len(s.drop_last());
    }
}

proof fn lemma_iff_all_zero(s: Seq<i32>)
    ensures (count_nonzero_spec(s) == 0) <==> (forall|i: int| 0 <= i < s.len() ==> s[i] == 0)
    decreases s.len()
{
    if s.len() > 0 {
        lemma_iff_all_zero(s.drop_last());
    }
}

proof fn lemma_iff_all_nonzero(s: Seq<i32>)
    ensures (count_nonzero_spec(s) == s.len()) <==> (forall|i: int| 0 <= i < s.len() ==> s[i] != 0)
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_le_len(s.drop_last());
        lemma_iff_all_nonzero(s.drop_last());
    }
}
// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i32>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type error and used new IFF lemmas to prove invariants */
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count as nat == count_nonzero_spec(a@.subrange(0, i as int)),
            count <= i,
            (forall|j: int| 0 <= j < i as int && a[j] == 0) ==> count == 0,
            (forall|j: int| 0 <= j < i as int && a[j] != 0) ==> count == i,
    {
        if a[i] != 0 {
            count = count + 1;
        }
        i = i + 1;
        proof {
            assert(count_nonzero_spec(a@.subrange(0, i as int)) ==
                   count_nonzero_spec(a@.subrange(0, (i - 1) as int)) + (if a@[(i - 1) as int] != 0 { 1nat } else { 0nat }));
            let sub = a@.subrange(0, i as int);
            lemma_count_le_len(sub);
            lemma_iff_all_zero(sub);
            lemma_iff_all_nonzero(sub);
        }
    }
    proof {
        lemma_count_le_len(a@);
        lemma_iff_all_zero(a@);
        lemma_iff_all_nonzero(a@);
    }
    count
}
// </vc-code>

}
fn main() {}