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
    /* code modified by LLM (iteration 2): implemented main logic with loop to compute string lengths */
    let mut result = Vec::with_capacity(a.len());
    let mut index = 0;
    while index < a.len()
        invariant
            result.len() == index,
            forall|k: int| 0 <= k < index ==> (result[k] as nat == a[k]@.len() && result[k] as nat >= 0 && (a[k]@.len() == 0 <==> a[k]@ == Seq::<char>::empty())),
        decreases a.len() - index,
    {
        result.push(a[index].len() as u8);
        proof {
            assert(result@.len() == index + 1);
            assert(result@[index] == a[index].len() as u8);
            assert(result@[index] as nat == a[index]@.len());
            assert(result@[index] as nat >= 0);
        }
        index += 1;
    }
    result
}
// </vc-code>

}
fn main() {}