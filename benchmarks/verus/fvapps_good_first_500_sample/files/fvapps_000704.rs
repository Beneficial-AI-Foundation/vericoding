// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn differentiate_polynomial(terms: Vec<(i32, u32)>) -> (result: String)
    ensures
        /* If all terms are constant (exponent 0) or empty, result is "0" */
        (terms.is_empty() || forall|i: int| 0 <= i < terms.len() ==> terms[i].1 == 0) ==> result@ == "0",
        /* Constant term (exponent 0) derivatives are 0 */
        terms.len() == 1 && terms[0].1 == 0 ==> result@ == "0",
        /* Linear term derivatives are just the coefficient */
        terms.len() == 1 && terms[0].1 == 1 && terms[0].0 != 0 ==> {
            result@.len() > 0
        },
        /* Higher power derivatives follow power rule: d/dx(ax^n) = (a*n)x^(n-1) */
        terms.len() == 1 && terms[0].0 != 0 && terms[0].1 > 1 ==> {
            let new_coef = terms[0].0 * (terms[0].1 as i32);
            let new_exp = terms[0].1 - 1;
            if new_exp == 0 {
                result@.len() > 0
            } else {
                result@.contains('x')
            }
        }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // /* Apps difficulty: interview */
    // /* Assurance level: unguarded */

    // /* Expected output: '2x^1' */
    // let result1 = differentiate_polynomial(vec![(1, 2)]);
    // println!("{}", result1);

    // /* Expected output: '3x^2 + 1' */
    // let result2 = differentiate_polynomial(vec![(1, 3), (1, 1), (1, 0)]);
    // println!("{}", result2);

    // /* Expected output: '0' */
    // let result3 = differentiate_polynomial(vec![(5, 0)]);
    // println!("{}", result3);
}