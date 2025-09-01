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
proof fn u64_add_u32_to_int(a: u64, b: u32)
    ensures ((a + (b as u64)) as int) == (a as int) + (b as int)
{
    assert(((a + (b as u64)) as int) == (a as int) + (b as int));
}
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
            (acc as int) == sum(numbers@[(0..(i as nat))]),
    {
        let x: u32 = numbers[i];
        let old_acc = acc;
        acc = old_acc + (x as u64);
        proof {
            u64_add_u32_to_int(old_acc, x);
        }
        // use the loop invariant for the previous i and the sequence property
        assert((old_acc as int) == sum(numbers@[(0..(i as nat))]));
        assert(sum(numbers@[(0..((i as nat) + 1))]) == sum(numbers@[(0..(i as nat))]) + (numbers@[i as nat] as int));
        assert((x as int) == (numbers@[i as nat] as int));
        assert((acc as int) == sum(numbers@[(0..((i as nat) + 1))]));
        i = i + 1;
    }

    (acc, None)
    // impl-end
}
// </vc-code>

fn main() {}
}