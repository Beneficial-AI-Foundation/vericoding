use vstd::prelude::*;

verus! {

spec fn seq_max(a: Seq<i32>) -> (ret: i32)
    decreases a.len(),
{
    if a.len() == 0 {
        i32::MIN
    } else if a.last() > seq_max(a.drop_last()) {
        a.last()
    } else {
        seq_max(a.drop_last())
    }
}

// <vc-helpers>
fn seq_max_push(s: Seq<i32>, x: i32)
    ensures seq_max(s.push(x)) == if x > seq_max(s) { x } else { seq_max(s) }
    decreases s.len()
{
    proof {
        // s.push(x) is non-empty, so use definition of seq_max on non-empty sequence
        assert(s.push(x).len() != 0);
        assert(seq_max(s.push(x)) ==
            (if s.push(x).last() > seq_max(s.push(x).drop_last()) {
                s.push(x).last()
            } else {
                seq_max(s.push(x).drop_last())
            }));
        // properties of push
        assert(s.push(x).last() == x);
        assert(s.push(x).drop_last() == s);
        // substitute
        assert(seq_max(s.push(x)) == (if x > seq_max(s) { x } else { seq_max(s) }));
    }
}

fn take_push(nums: Seq<i32>, i: int)
    requires 0 <= i && i < nums.len()
    ensures nums.take(i).push(nums[i]) == nums.take(i + 1)
    decreases nums.len() - i
{
    proof {
        // take(i+1) equals take(i) with the i-th element appended
        assert(nums.take(i + 1) == nums.take(i).push(nums[i]));
    }
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut result: Vec<i32> = Vec::new();
    let mut cur_max: i32 = i32::MIN;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < (i as int) ==> result[j] == seq_max(numbers@.take(j + 1)),
            cur_max == seq_max(numbers@.take(i as int)),
        decreases numbers.len() - i
    {
        let idx: usize = i;
        let x: i32 = numbers[idx];
        if x > cur_max {
            cur_max = x;
        }
        result.push(cur_max);
        // prove updated cur_max equals seq_max(numbers@.take(i+1))
        proof {
            // i < numbers.len() is ensured by loop condition
            assert(i < numbers.len());
            assert((i as int) < numbers@.len());
            take_push(numbers@, i as int);
            seq_max_push(numbers@.take(i as int), numbers@[i as int]);
            // from seq_max_push and take_push, conclude
            assert(numbers@.take(i as int).push(numbers@[i as int]) == numbers@.take((i as int) + 1));
            assert(seq_max(numbers@.take(i as int).push(numbers@[i as int])) ==
                   (if numbers@[i as int] > seq_max(numbers@.take(i as int)) { numbers@[i as int] } else { seq_max(numbers@.take(i as int)) }));
            // cur_max was updated to be the max of previous cur_max and numbers@[i]
            assert(cur_max == (if numbers@[i as int] > seq_max(numbers@.take(i as int)) { numbers@[i as int] } else { seq_max(numbers@.take(i as int)) }));
            assert(cur_max == seq_max(numbers@.take((i as int) + 1)));
        }
        i = i + 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}