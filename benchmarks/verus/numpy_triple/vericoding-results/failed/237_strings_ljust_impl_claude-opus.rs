// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ljust(a: Vec<String>, width: u8, fillchar: char) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() == if a[i]@.len() >= width as nat { a[i]@.len() } else { width as nat },
        forall|i: int| 0 <= i < a.len() && a[i]@.len() >= width as nat ==> #[trigger] result[i]@ == a[i]@,
        forall|i: int| 0 <= i < a.len() && a[i]@.len() < width as nat ==> {
            &&& #[trigger] result[i]@.len() == width as nat
            &&& result[i]@.subrange(0, a[i]@.len() as int) == a[i]@
        },
        forall|i: int| 0 <= i < a.len() && a[i]@.len() == 0 ==> #[trigger] result[i]@.len() == width as nat
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches - use nat consistently in ghost comparisons */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j]@.len() == if a[j]@.len() >= width as nat { a[j]@.len() } else { width as nat },
            forall|j: int| 0 <= j < i && a[j]@.len() >= width as nat ==> #[trigger] result[j]@ == a[j]@,
            forall|j: int| 0 <= j < i && a[j]@.len() < width as nat ==> {
                &&& #[trigger] result[j]@.len() == width as nat
                &&& result[j]@.subrange(0, a[j]@.len() as int) == a[j]@
            },
            forall|j: int| 0 <= j < i && a[j]@.len() == 0 ==> #[trigger] result[j]@.len() == width as nat,
    {
        let s = &a[i];
        
        if s@.len() >= width as nat {
            result.push(s.clone());
        } else {
            let mut padded = s.clone();
            let padding_needed = (width as nat - s@.len()) as usize;
            let mut j: usize = 0;
            
            while j < padding_needed
                invariant
                    0 <= j <= padding_needed,
                    padding_needed == (width as nat - s@.len()) as usize,
                    padded@.len() == s@.len() + j as nat,
                    padded@.subrange(0, s@.len() as int) == s@,
            {
                padded = padded + fillchar.to_string().as_str();
                j = j + 1;
            }
            
            result.push(padded);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}