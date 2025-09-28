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
spec fn has_no_even_digit_exec(n: u8) -> bool
    decreases n as int
{
    if n < 10 {
        n % 2 == 1
    } else {
        n % 2 == 1 && has_no_even_digit_exec(n / 10)
    }
}

/* helper modified by LLM (iteration 2): prove equivalence between spec and exec versions */
proof fn lemma_has_no_even_digit_equiv(n: u8)
    ensures has_no_even_digit_exec(n) == has_no_even_digit(n as int)
    decreases n as int
{
    if n >= 10 {
        lemma_has_no_even_digit_equiv(n / 10);
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
{
    /* code modified by LLM (iteration 2): use executable version of has_no_even_digit */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            forall|j: int| 0 <= j < result@.len() ==> has_no_even_digit(result@[j] as int),
            forall|j: int, k: int| 0 <= j < k < result@.len() ==> result@[j] <= result@[k],
            forall|e: u8| result@.contains(e) ==> x@.subrange(0, i as int).contains(e),
            forall|e: u8| x@.subrange(0, i as int).contains(e) && has_no_even_digit(e as int) ==> result@.contains(e)
    {
        if has_no_even_digit_exec(x[i]) {
            proof {
                lemma_has_no_even_digit_equiv(x[i]);
            }
            let mut already_added = false;
            let mut j = 0;
            while j < result.len()
                invariant
                    0 <= j <= result.len(),
                    already_added ==> exists|k: int| 0 <= k < j && result@[k] == x[i],
                    !already_added ==> forall|k: int| 0 <= k < j ==> result@[k] != x[i]
            {
                if result[j] == x[i] {
                    already_added = true;
                    break;
                }
                j = j + 1;
            }
            
            if !already_added {
                let mut insert_pos = 0;
                let mut k = 0;
                while k < result.len()
                    invariant
                        0 <= k <= result.len(),
                        insert_pos <= k,
                        forall|m: int| 0 <= m < insert_pos ==> result@[m] <= x[i]
                {
                    if result[k] <= x[i] {
                        insert_pos = k + 1;
                    }
                    k = k + 1;
                }
                result.insert(insert_pos, x[i]);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}