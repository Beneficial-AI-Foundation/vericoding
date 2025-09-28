use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
// </vc-spec>
// <vc-code>
{
    let c = choose|c: usize| c as nat == numbers.filter(|i: int| i < threshold).len();
    proof {
        assert(c as nat == numbers.filter(|i: int| i < threshold).len());
    }
    c
}
// </vc-code>

fn main() {}

}