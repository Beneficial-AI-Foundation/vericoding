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
proof fn sum_append_single(s: Seq<u32>, i: int)
    requires 0 <= i < s.len(),
    ensures s.subrange(0, i+1) == s.subrange(0, i).push(s[i]),
    ensures sum(s.subrange(0, i+1)) == sum(s.subrange(0, i)) + s[i] as int
{
    assert(s.subrange(0, i+1) == s.subrange(0, i).push(s[i]));
    assert(sum(s.subrange(0, i+1)) == sum(s.subrange(0, i).push(s[i])));
    assert(sum(s.subrange(0, i).push(s[i])) == sum(s.subrange(0, i)) + s[i] as int);
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
    let mut total: u64 = 0;
    for i in 0..numbers.len()
        invariant
            total as int == sum(numbers@.subrange(0, i as int))
    {
        let old_total = total;
        total = total + numbers[i] as u64;

        proof {
            sum_append_single(numbers@, i as int);
            assert(total as int == old_total as int + (numbers[i] as int));
            assert(old_total as int == sum(numbers@.subrange(0, i as int)));
            assert(total as int == sum(numbers@.subrange(0, i as int)) + (numbers[i] as int));
            assert(total as int == sum(numbers@.subrange(0, (i+1) as int)));
        }
    }
    (total, None)
}
// </vc-code>

fn main() {}
}