// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added 'open' keyword to fix compilation error */
pub open spec fn spec_count_nonzero(s: Seq<i8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s.last() != 0 { 1 } else { 0 }) + spec_count_nonzero(s.drop_last())
    }
}

proof fn lemma_spec_count_push(s: Seq<i8>, elem: i8)
    ensures
        spec_count_nonzero(s.push(elem)) == spec_count_nonzero(s) + (if elem != 0 { 1 } else { 0 }),
{
}

proof fn lemma_count_le_len(s: Seq<i8>)
    ensures
        spec_count_nonzero(s) <= s.len(),
    decreases s.len(),
{
    if !s.is_empty() {
        lemma_count_le_len(s.drop_last());
    }
}

proof fn lemma_all_zero(s: Seq<i8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] == 0,
    ensures
        spec_count_nonzero(s) == 0,
    decreases s.len(),
{
    if !s.is_empty() {
        lemma_all_zero(s.drop_last());
    }
}

proof fn lemma_all_nonzero(s: Seq<i8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] != 0,
    ensures
        spec_count_nonzero(s) == s.len(),
    decreases s.len(),
{
    if !s.is_empty() {
        lemma_all_nonzero(s.drop_last());
    }
}

proof fn lemma_exists_nonzero(s: Seq<i8>)
    requires
        exists|i: int| 0 <= i < s.len() && s[i] != 0,
    ensures
        spec_count_nonzero(s) > 0,
    decreases s.len(),
{
    if !s.is_empty() {
        if s.last() == 0 {
            lemma_exists_nonzero(s.drop_last());
        }
    }
}

proof fn lemma_exists_zero(s: Seq<i8>)
    requires
        exists|i: int| 0 <= i < s.len() && s[i] == 0,
    ensures
        spec_count_nonzero(s) < s.len(),
    decreases s.len(),
{
    if !s.is_empty() {
        lemma_count_le_len(s.drop_last());
        if s.last() != 0 {
            lemma_exists_zero(s.drop_last());
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i8>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a@.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a@.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a@.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a@.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): No changes made to the code, only fixed compilation error in helpers. */
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == spec_count_nonzero(a@.subrange(0, i as int)) as usize,
        decreases a.len() - i
    {
        proof {
            lemma_spec_count_push(a@.subrange(0, i as int), a@[i as int]);
        }
        if a[i] != 0 {
            count = count + 1;
        }
        i = i + 1;
    }

    proof {
        lemma_count_le_len(a@);
        if forall|j: int| 0 <= j < a@.len() ==> a@[j] == 0 {
            lemma_all_zero(a@);
        }
        if forall|j: int| 0 <= j < a@.len() ==> a@[j] != 0 {
            lemma_all_nonzero(a@);
        }
        if exists|j: int| 0 <= j < a@.len() && a@[j] != 0 {
            lemma_exists_nonzero(a@);
        }
        if exists|j: int| 0 <= j < a@.len() && a@[j] == 0 {
            lemma_exists_zero(a@);
        }
    }
    
    count
}

// </vc-code>

}
fn main() {}