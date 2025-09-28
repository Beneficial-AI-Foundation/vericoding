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
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& result[j] as nat == a[j]@.len()
                &&& result[j] as nat >= 0
                &&& (a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty())
            }
    {
        let len = a[i].unicode_len();
        assert(len >= 0);
        assert(len <= u8::MAX as usize);
        let len_u8: u8 = len as u8;
        assert(len_u8 as nat == a[i]@.len());
        assert(a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty());
        result.push(len_u8);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}