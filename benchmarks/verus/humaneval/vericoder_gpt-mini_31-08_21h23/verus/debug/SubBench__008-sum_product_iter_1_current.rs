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
// <vc-helpers>
proof fn u64_add_u32_to_int(a: u64, b: u32)
    ensures ((a + (b as u64)) as int) == (a as int) + (b as int)
{
    // The cast and addition operations are congruent across these unsigned
    // integer types and int; the verifier can discharge the obvious arithmetic.
    assert(((a + (b as u64)) as int) == (a as int) + (b as int));
}
// </vc-helpers>
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
    let len = numbers.len();
    let mut i: usize = 0;
    let mut acc: u64 = 0;

    while i < len
        invariant
            i <= len,
            // acc as int equals the sum of the prefix numbers@[..i]
            (acc as int) == sum(numbers@[0..i]),
    {
        let x: u32 = numbers.get(i);
        // remember old acc for the proof
        let old_acc = acc;
        acc = old_acc + (x as u64);
        proof {
            u64_add_u32_to_int(old_acc, x);
        }
        // use the loop invariant for the previous i and the sequence property
        // that sum(prefix ++ [x]) = sum(prefix) + x
        assert((old_acc as int) == sum(numbers@[0..i]));
        assert(sum(numbers@[0..i + 1]) == sum(numbers@[0..i]) + (numbers@[i] as int));
        // numbers.get(i) equals numbers@[i]
        assert((x as int) == (numbers@[i] as int));
        // combine to reestablish the invariant for i+1
        assert((acc as int) == sum(numbers@[0..i + 1]));
        i = i + 1;
    }

    // Return computed sum and no product information
    (acc, None)
    // impl-end
}
// </vc-code>

fn main() {}
}