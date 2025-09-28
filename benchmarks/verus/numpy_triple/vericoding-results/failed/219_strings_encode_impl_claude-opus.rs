// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn encode(a: Vec<Vec<char>>, encoding: Vec<char>, errors: Vec<char>) -> (result: Vec<Vec<u8>>)
    ensures
        result@.len() == a@.len(),
        /* Deterministic encoding: same input produces same output */
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < a@.len() && a@[i] == a@[j] ==> result@[i] == result@[j],
        /* Empty strings encode to empty byte arrays */
        forall|i: int| 0 <= i < a@.len() && a@[i].len() == 0 ==> result@[i].len() == 0,
        /* Non-empty strings produce non-empty byte arrays */
        forall|i: int| 0 <= i < a@.len() && a@[i].len() > 0 ==> result@[i].len() > 0,
        /* For UTF-8 encoding, encoded size is at least the string length */
        forall|i: int| 0 <= i < a@.len() ==> result@[i].len() >= a@[i].len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type error by casting a[i].len() to int in invariant */
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j].len() >= a@[j].len(),
            forall|j: int| 0 <= j < i && a@[j].len() == 0 ==> result@[j].len() == 0,
            forall|j: int| 0 <= j < i && a@[j].len() > 0 ==> result@[j].len() > 0,
            forall|j1: int, j2: int| 0 <= j1 < i && 0 <= j2 < i && a@[j1] == a@[j2] ==> result@[j1] == result@[j2],
    {
        let mut encoded: Vec<u8> = Vec::new();
        let mut k: usize = 0;
        while k < a[i].len()
            invariant
                0 <= k <= a[i].len(),
                encoded.len() == k,
                encoded@.len() == k as int,
                encoded@.len() >= k as int,
        {
            let c = a[i][k];
            encoded.push(c as u8);
            k = k + 1;
        }
        result.push(encoded);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}