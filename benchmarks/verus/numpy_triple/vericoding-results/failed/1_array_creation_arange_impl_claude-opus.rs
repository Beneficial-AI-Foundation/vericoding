// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn arange(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires step != 0,
    ensures
        result.len() == n,
        n == 0 ==> ((step > 0 && start >= stop) || (step < 0 && start <= stop)),
        n > 0 ==> (
            forall|i: int| 0 <= i < n ==> result@[i] == start as int + i * step as int
        ),
        n > 0 && step > 0 ==> (
            start < stop &&
            forall|i: int| 0 <= i < n ==> result@[i] < stop as int
        ),
        n > 0 && step < 0 ==> (
            start > stop &&
            forall|i: int| 0 <= i < n ==> result@[i] > stop as int
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix invariant syntax - use commas instead of && for multi-line conditions */
    let mut result: Vec<i8> = Vec::new();
    let mut current = start;
    let mut i: usize = 0;
    
    if n == 0 {
        // Handle empty case explicitly
        return result;
    }
    
    // At this point n > 0
    assert(n > 0);
    
    while i < n
        invariant
            result.len() == i,
            i <= n,
            n > 0,
            current as int == start as int + i as int * step as int,
            forall|j: int| 0 <= j < i ==> result@[j] == start as int + j * step as int,
            step > 0 ==> start < stop,
            step > 0 ==> current as int < stop as int,
            step > 0 ==> forall|j: int| 0 <= j < i ==> result@[j] < stop as int,
            step < 0 ==> start > stop,
            step < 0 ==> current as int > stop as int,
            step < 0 ==> forall|j: int| 0 <= j < i ==> result@[j] > stop as int,
            i < n && step > 0 ==> current as int + step as int < 128,
            i < n && step < 0 ==> current as int + step as int >= -128,
        decreases n - i
    {
        result.push(current);
        
        if i + 1 < n {
            // Only update current if we're not at the last iteration
            assert(current as int + step as int < 128 || current as int + step as int >= -128);
            current = (current as int + step as int) as i8;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}