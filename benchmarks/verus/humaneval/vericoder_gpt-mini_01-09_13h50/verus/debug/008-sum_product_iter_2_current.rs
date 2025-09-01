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
// No helpers needed for this proof.
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
    while i < numbers.len()
        invariant i <= numbers.len(),
        invariant (acc as int) == sum(numbers@[0..i])
    {
        let v: u32 = numbers.index(i);
        acc = acc + (v as u64);
        i = i + 1;
        assert((acc as int) == sum(numbers@[0..i]));
    }
    (acc, None)
    // impl-end
}
// </vc-code>

fn main() {}
}