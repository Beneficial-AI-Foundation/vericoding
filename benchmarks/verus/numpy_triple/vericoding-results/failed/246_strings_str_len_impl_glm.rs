// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): fix non-primitive cast by converting nat to int then to u8 */
    let mut result = Vec::with_capacity(a.len());
    for i in 0..a.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as nat == a[j]@.len(),
            forall|j: int| 0 <= j < i ==> result[j] as nat >= 0,
            forall|j: int| 0 <= j < i ==> (a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty()),
        decreases a.len() - i
    {
        let s = &a[i];
        let len_nat = s@.len();
        let len_int = len_nat as int;
        let len_u8 = len_int as u8;
        proof {
            assert(len_u8 as nat == len_nat);
            assert(len_nat >= 0);
            assert((len_nat == 0) == (s@.len() == 0));
            assert((len_nat == 0) == (s@ == Seq::<char>::empty()));
        }
        result.push(len_u8);
    }
    result
}
// </vc-code>

}
fn main() {}