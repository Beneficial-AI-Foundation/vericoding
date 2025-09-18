// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove problematic helpers and add correct type conversions */
fn spec_nat_to_usize(len: nat) -> usize { len as usize }

ghost fn string_len_lemma(s: String) 
    ensures 
        s@.len() >= 0,
        s@.len() == 0 <==> s@ == Seq::<char>::empty()
{
    if s@.len() == 0 {
        assert(s@ == Seq::<char>::empty());
    } else {
        assert(s@ != Seq::<char>::empty());
    }
}
// </vc-helpers>

// <vc-spec>
fn str_len(a: Vec<String>) -> (result: Vec<nat>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& result[i] == a[i]@.len()
            &&& result[i] >= 0
            &&& (a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty())
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix type errors by using proper ghost context and correct loop invariant */
{
    let mut result: Vec<nat> = Vec::new();
    let n = a.len();
    ghost {
        let mut i: int = 0;
        while i < n as int
            invariant
                result@.len() == i as usize,
                forall|j: int| 0 <= j < i ==> {
                    &&& result@[j as usize] as int == a@[j as usize]@.len()
                    &&& result@[j as usize] >= 0
                    &&& (a@[j as usize]@.len() == 0 <==> a@[j as usize]@ == Seq::<char>::empty())
                },
        {
            string_len_lemma(a[i as usize].clone());
            i = i + 1;
        }
    }
    
    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                &&& result[j] == a[j]@.len()
                &&& result[j] >= 0
                &&& (a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty())
            },
    {
        result.push(a[i]@.len());
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}