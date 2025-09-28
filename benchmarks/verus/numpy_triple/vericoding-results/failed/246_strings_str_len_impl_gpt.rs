// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide a trivial helper to keep helpers section valid without imposing additional proof obligations */
proof fn helper_trivial() { }

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
    /* code modified by LLM (iteration 5): fix spec/executable index type mismatches by using sequence views (@) and int casts in invariants/assertions */
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] as nat == a@[j]@.len(),
        decreases a.len() - i
    {
        let l: usize = a[i].len();
        let b: u8 = l as u8;
        result.push(b);
        proof {
            // From the spec of String::len(): l as int equals the length of the spec view
            assert(l as int == a@[i as int]@.len());
            // After push, the new element at index i equals b
            assert(result@[i as int] == b);
            // Therefore, the invariant clause for j == i holds
            assert(result@[i as int] as nat == a@[i as int]@.len());
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}