// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add helper to get string length as nat for proper type compatibility */
fn string_len_as_nat(s: &String) -> (len: nat)
    ensures len == s@.len()
{
    s.as_str().unicode_len() as nat
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
    /* code modified by LLM (iteration 5): Fix type mismatch by using nat helper instead of usize */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& result[j] as nat == a[j]@.len()
                &&& result[j] as nat >= 0
                &&& (a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty())
            },
        decreases a.len() - i
    {
        let len = string_len_as_nat(&a[i]);
        let byte_len = if len <= u8::MAX as nat {
            len as u8
        } else {
            u8::MAX
        };
        
        proof {
            assert(byte_len as nat <= u8::MAX as nat);
            assert(byte_len as nat >= 0);
            if len <= u8::MAX as nat {
                assert(byte_len as nat == a[i]@.len());
            } else {
                assert(byte_len as nat == u8::MAX as nat);
            }
        }
        
        result.push(byte_len);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}