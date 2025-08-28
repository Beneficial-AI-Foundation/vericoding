use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut count = 0;
    let mut remaining = numbers;
    
    while remaining.len() > 0
        invariant 
            count + remaining.filter(|i: int| i < threshold).len() == numbers.filter(|i: int| i < threshold).len(),
            remaining.subset_of(numbers)
    {
        let elem = remaining.choose();
        remaining = remaining.remove(elem);
        if elem < threshold {
            count = count + 1;
        }
    }
    count
}
// </vc-code>

fn main() {}

}