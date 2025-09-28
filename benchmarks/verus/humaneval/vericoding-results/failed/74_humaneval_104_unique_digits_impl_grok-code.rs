// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_no_even_digit(n: int) -> bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && has_no_even_digit(n / 10)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Changed from pub fn to fn to allow reference to private spec fn in ensures clause */
fn exec_has_no_even_digit(n: u8) -> (r: bool)
    ensures
        r <==> has_no_even_digit(n as int),
    decreases n
{
    if n < 10 {
        n % 2 == 1
    } else {
        n % 2 == 1 && exec_has_no_even_digit(n / 10)
    }
}
// </vc-helpers>

// <vc-spec>
fn unique_digits(x: Vec<u8>) -> (result: Vec<u8>)
  ensures 
    forall|i: int| 0 <= i < result@.len() ==> has_no_even_digit(result@[i] as int) &&
    forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] <= result@[j] &&
    forall|e: u8| x@.contains(e) && has_no_even_digit(e as int) ==> result@.contains(e) &&
    forall|e: u8| result@.contains(e) ==> x@.contains(e)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implemented main logic using helper function */
{
    let mut selected = [false; 256];
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x@.len(),
        decreases
            x@.len() - i
    {
        let e = x[i];
        if exec_has_no_even_digit(e) && !selected[e as usize] {
            selected[e as usize] = true;
        }
        i += 1;
    }
    let mut result = Vec::new();
    let mut k = 0;
    while k < 256
        invariant
            k <= 256,
        decreases
            256 - k
    {
        if selected[k] {
            result.push(k as u8);
        }
        k += 1;
    }
    result
}
// </vc-code>


}

fn main() {}