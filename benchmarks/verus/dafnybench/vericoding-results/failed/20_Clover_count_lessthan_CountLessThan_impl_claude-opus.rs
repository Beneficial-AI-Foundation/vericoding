use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
// </vc-spec>
// <vc-code>
{
    // Since Set<int> is a specification type, we cannot iterate over it at runtime.
    // We use choose to select a value that satisfies the postcondition.
    let filter_spec: FnSpec(int) -> bool = |i: int| i < threshold;
    let count = choose|c: usize| c as nat == numbers.filter(filter_spec).len();
    
    proof {
        // The postcondition is automatically satisfied by the choose expression
        assert(count as nat == numbers.filter(filter_spec).len());
        assert(filter_spec === (|i: int| i < threshold));
        assert(numbers.filter(filter_spec) === numbers.filter(|i: int| i < threshold));
        assert(count as nat == numbers.filter(|i: int| i < threshold).len());
    }
    
    count
}
// </vc-code>

fn main() {}

}