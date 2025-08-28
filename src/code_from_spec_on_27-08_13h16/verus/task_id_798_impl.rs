use vstd::prelude::*;

verus! {

spec fn sum_to(arr: Seq<i64>) -> (result: int)
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}
// pure-end

// <vc-helpers>
proof fn sum_to_non_negative(arr: Seq<i64>)
    requires
        forall|i: int| 0 <= i < arr.len() ==> arr[i] >= 0,
    ensures
        sum_to(arr) >= 0,
    decreases arr.len(),
{
    if arr.len() == 0 {
    } else {
        sum_to_non_negative(arr.drop_last());
    }
}

proof fn sum_to_subrange(arr: Seq<i64>, end: int)
    requires
        0 <= end <= arr.len(),
    ensures
        sum_to(arr.subrange(0, end)) == sum_to(arr.take(end)),
    decreases end,
{
    if end == 0 {
    } else {
        sum_to_subrange(arr, end - 1);
    }
}

proof fn sum_to_additive(arr: Seq<i64>, i: int)
    requires
        0 <= i < arr.len(),
    ensures
        sum_to(arr.subrange(0, i + 1)) == sum_to(arr.subrange(0, i)) + arr[i],
    decreases i,
{
    if i == 0 {
        assert(arr.subrange(0, 1) =~= Seq::new(1, |j: int| arr[0]));
        assert(sum_to(arr.subrange(0, 1)) == arr[0]);
        assert(sum_to(arr.subrange(0, 0)) == 0);
    } else {
        sum_to_additive(arr, i - 1);
        assert(arr.subrange(0, i + 1) =~= arr.subrange(0, i).push(arr[i]));
        assert(sum_to(arr.subrange(0, i + 1)) == sum_to(arr.subrange(0, i)) + arr[i]);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum(arr: &Vec<i64>) -> (sum: i128)
    // post-conditions-start
    ensures
        sum_to(arr@) == sum,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut sum: i128 = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum == sum_to(arr@.subrange(0, i as int)),
        decreases arr.len() - i,
    {
        let next_sum: i128 = sum + arr@[i] as i128;
        proof {
            sum_to_additive(arr@, i as int);
            assert(sum_to(arr@.subrange(0, i as int + 1)) == sum_to(arr@.subrange(0, i as int)) + arr@[i]);
        }
        sum = next_sum;
        i = i + 1;
    }
    sum
}
// </vc-code>

} // verus!

fn main() {}