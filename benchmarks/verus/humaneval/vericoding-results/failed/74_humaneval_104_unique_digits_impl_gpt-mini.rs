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
/* helper modified by LLM (iteration 2): u8_range ensures u8 is within 0..256 */
lemma u8_range(e: u8)
    ensures
        0 <= e as int && e as int < 256,
{
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
{
    /* code modified by LLM (iteration 2): build sorted unique vector of digits with no even digits */
    let mut result: Vec<u8> = Vec::new();
    let n: int = x.len() as int;
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| 0 <= k < result@.len() ==> has_no_even_digit(result@[k] as int),
            forall|a: int, b: int| 0 <= a < b < result@.len() ==> result@[a] <= result@[b],
            forall|e: u8| result@.contains(e) ==> exists|j: int| 0 <= j < i && x@[j] == e && has_no_even_digit(e as int),
            forall|j: int| 0 <= j < i && has_no_even_digit(x@[j] as int) ==> result@.contains(x@[j]),
        decreases
            n - i
    {
        let e: u8 = x[i as usize];
        if has_no_even_digit(e as int) {
            // check if e already in result
            let mut found: bool = false;
            let mut k: int = 0;
            while k < result.len() as int
                invariant
                    0 <= k <= result.len() as int,
                    found == (exists|t: int| 0 <= t < k && result@[t] == e),
                decreases
                    result.len() as int - k
            {
                if result[k as usize] == e {
                    found = true;
                }
                k += 1;
            }

            if !found {
                // find insertion position to keep nondecreasing order
                let mut pos: int = 0;
                while pos < result.len() as int && result[pos as usize] <= e
                    invariant
                        0 <= pos <= result.len() as int,
                        forall|t: int| 0 <= t < pos ==> result@[t] <= e,
                    decreases
                        result.len() as int - pos
                {
                    pos += 1;
                }
                result.insert(pos as usize, e);
            }
        }
        i += 1;
    }
    result
}

// </vc-code>


}

fn main() {}