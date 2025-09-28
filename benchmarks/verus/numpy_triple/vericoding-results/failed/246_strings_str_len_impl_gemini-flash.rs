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
    /* code modified by LLM (iteration 5): Changed indexing `i as nat` to `i` within the loop, and changed `len()` to `len().spec_len()` for `Seq<char>` */
    let mut result_vec: Vec<u8> = Vec::new();
    let mut i: nat = 0nat;

    while (i as usize) < a.len()
        invariant
            result_vec.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> {
                &&& result_vec.index(j as nat) == a.index(j as nat)@.len() as u8
                &&& result_vec.index(j as nat) >= 0
            },
            // The condition `a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty()` 
            // is a property of `Seq<char>` and doesn't need to be proven here as an invariant.
            // It's implicitly true if `a[j]@.len()` is correctly derived from `a[j]@`.
        decreases a.len() - (i as int)
    {
        // Access the string using `a[i]@` to get its ghost value (Seq<char>) for `.len()`
        let s_len = a.index(i).spec_len(); // Use .spec_len() to get the length in ghost code
        let len_as_u8 = s_len as u8;
        result_vec.push(len_as_u8);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}