// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): s.len() non-negativity */
fn seq_len_nonneg(s: Seq<char>)
    ensures
        s.len() >= 0,
{
    proof {
        assert(s.len() >= 0);
    }
}

/* helper modified by LLM (iteration 5): empty sequence iff len zero */
fn seq_empty_iff_len_zero(s: Seq<char>)
    ensures
        s.len() == 0 <==> s == Seq::<char>::empty(),
{
    proof {
        assert(s.len() == 0 ==> s == Seq::<char>::empty());
        assert(s == Seq::<char>::empty() ==> s.len() == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn str_len(a: Vec<String>) -> (result: Vec<u8>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& result[i] as nat == a[i]@.len()
            &&& result[i] as nat >= 0
            &&& (a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty())
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use nat for length to match Seq.len() */
    let mut result: Vec<u8> = Vec::new();
    let mut i_usize: usize = 0;
    let n_usize: usize = a.len();
    while i_usize < n_usize
        invariant
            result.len() == i_usize,
            forall|j: int| 0 <= j < i_usize as int ==> {
                &&& result[j] as nat == a[j]@.len()
                &&& result[j] as nat >= 0
                &&& (a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty())
            },
        decreases n_usize - i_usize
    {
        let l: nat = a[i_usize]@.len();
        result.push(l as u8);
        i_usize = i_usize + 1;
    }
    result
}
// </vc-code>

}
fn main() {}