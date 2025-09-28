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
/* helper modified by LLM (iteration 5): Fixed invariants and added proper sorting verification */
fn filter_even_digits(vec: Vec<u8>) -> (result: Vec<u8>)
    ensures
        forall|i: int| 0 <= i < result@.len() ==> has_no_even_digit(result@[i] as int),
        forall|e: u8| result@.contains(e) ==> vec@.contains(e) && has_no_even_digit(e as int)
{
    let mut filtered = Vec::new();
    let mut i: usize = 0;
    
    while i < vec.len()
        invariant
            0 <= i <= vec@.len(),
            forall|j: int| 0 <= j < filtered@.len() ==> has_no_even_digit(filtered@[j] as int),
            forall|e: u8| filtered@.contains(e) ==> vec@.contains(e) && has_no_even_digit(e as int)
        decreases (vec@.len() as int) - (i as int)
    {
        let elem = vec[i];
        if !is_even_digit(elem) {
            filtered.push(elem);
        }
        i += 1;
    }
    filtered
}

proof fn lemma_swap_preserves_invariants(seq: Seq<u8>, i: int, j: int, min_index: int)
    requires
        0 <= i <= j < seq.len(),
        0 <= min_index < seq.len(),
        forall|k: int| i <= k < j ==> seq[min_index] <= seq[k]
    ensures
        forall|k: int| i <= k < j ==> seq.swap(i, min_index)@[min_index] <= seq.swap(i, min_index)@[k]
{
}

spec fn is_sorted_range(seq: Seq<u8>, start: int, end: int) -> bool {
    forall|i: int, j: int| start <= i < j < end ==> seq[i] <= seq[j]
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
    /* code modified by LLM (iteration 5): Fixed loop invariants and index bounds */
    let mut filtered = filter_even_digits(x);
    let mut i: usize = 0;
    
    while i < filtered.len()
        invariant
            0 <= i <= filtered@.len(),
            is_sorted_range(filtered@, 0, i as int),
            forall|j: int| 0 <= j < filtered@.len() ==> has_no_even_digit(filtered@[j] as int)
        decreases (filtered@.len() as int) - (i as int)
    {
        let mut j: usize = i;
        let mut min_index: usize = i;
        
        while j < filtered.len()
            invariant
                i <= j <= filtered@.len(),
                i <= min_index < filtered@.len(),
                forall|k: int| i <= k < j as int ==> filtered@[min_index as int] <= filtered@[k]
            decreases (filtered@.len() as int) - (j as int)
        {
            if filtered[j] < filtered[min_index] {
                min_index = j;
            }
            j += 1;
        }
        
        if min_index != i {
            let temp = filtered[i];
            filtered[i] = filtered[min_index];
            filtered[min_index] = temp;
        }
        i += 1;
    }
    filtered
}
// </vc-code>


}

fn main() {}