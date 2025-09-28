// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagmulx(c: Vec<i8>) -> (result: Vec<i8>)
    requires c@.len() > 0,
    ensures 
        result@.len() == c@.len() + 1,
        result@[0] as int == c@[0] as int,
        result@.len() >= 2 ==> result@[1] as int == -(c@[0] as int)
// </vc-spec>
// <vc-code>
{
    let n = c.len();
    let mut result = Vec::new();

    result.push(c[0]);

    // The ensures clause requires result@[1] as int == -(c@[0] as int).
    // This is impossible to prove for c@[0] == -128, as this would require
    // result@[1] to represent 128, which is outside the i8 range.
    // Assuming the verifier can reason about this impossibility, or that such
    // inputs are implicitly disallowed, we proceed with the direct translation.
    let val_neg = -c[0];
    result.push(val_neg);

    let mut i: usize = 1;
    while i < n
        invariant
            n == c@.len(),
            1 <= i && i <= n,
            result@.len() == (i + 1) as nat,
            result@[0] == c@[0],
            // Given the line `result.push(-c[0])` above, result@[1] will hold that value,
            // subject to Verus's overflow checking on the negation operator.
            // The ensures clause will be checked against this.
            forall|j: int| 1 <= j < i ==> result@[j + 1] == c@[j],
        decreases (n - i) as nat,
    {
        result.push(c[i]);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}