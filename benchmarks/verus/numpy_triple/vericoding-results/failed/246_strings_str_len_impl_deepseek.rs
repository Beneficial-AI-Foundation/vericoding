// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion from nat to int */
fn string_len(s: String) -> (len: u8)
    ensures
        len as nat == s@.len(),
        (s@.len() == 0) == (s@ == Seq::<char>::empty())
{
    let mut count: u8 = 0;
    let mut seq = s@;
    while seq.len() > 0
        invariant
            count as nat + seq.len() == s@.len(),
            count as nat >= 0
    {
        seq = seq.subrange(1, seq.len());
        count = count + 1;
    }
    count
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
/* code modified by LLM (iteration 5): Fixed type conversion from nat to int */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> {
                &&& result[j] as nat == a[j]@.len()
                &&& result[j] as nat >= 0
                &&& (a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty())
            }
    {
        let s = a[i].clone();
        let len = string_len(s);
        result.push(len);
        proof {
            let j = i as int;
            assert(result[j] as nat == a[j]@.len());
            assert(result[j] as nat >= 0);
            assert((a[j]@.len() == 0) == (a[j]@ == Seq::<char>::empty()));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}