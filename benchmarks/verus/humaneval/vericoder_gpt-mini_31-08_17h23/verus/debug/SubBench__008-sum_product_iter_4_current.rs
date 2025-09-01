use vstd::prelude::*;

verus! {

spec fn sum(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}
// pure-end
// pure-end

spec fn product(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(1, |acc: int, x| acc * x)
}
// pure-end

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))
    // pre-conditions-start
    requires
        numbers.len() < u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.0 == sum(numbers@),
        result.1 matches Some(v) ==> v == product(numbers@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut i: usize = 0usize;
    let mut acc: u64 = 0u64;
    proof {
        // base case: empty prefix has sum 0
        assert((acc as int) == sum(numbers@[..i]));
    }
    while i < numbers.len()
        invariant i <= numbers.len();
        invariant (acc as int) == sum(numbers@[..i]);
        decreases numbers.len() - i;
    {
        let x: u32 = numbers[i];
        acc = acc + (x as u64);
        i += 1;
        proof {
            // maintain the invariant after the step
            assert((acc as int) == sum(numbers@[..i]));
        }
    }
    proof {
        // by the invariant when i == numbers.len(), acc as int == sum(numbers@)
        assert((acc as int) == sum(numbers@));
    }
    (acc, None)
    // impl-end
}
// </vc-code>

fn main() {}
}