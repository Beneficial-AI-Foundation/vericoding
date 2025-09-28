use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// <vc-helpers>
spec fn max_int(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

proof fn lemma_max_one_of(a: int, b: int)
{
    if a >= b {
        assert(max_int(a, b) == a);
    } else {
        assert(max_int(a, b) == b);
    }
}

proof fn lemma_step(i: int, nums: Seq<int>, prev: int)
    requires
        0 < i,
        i < nums.len(),
        isMax(prev, nums.subrange(0, i)),
    ensures
        isMax(max_int(prev, nums[i]), nums.subrange(0, i + 1))
{
    let m = max_int(prev, nums[i]);

    // m is either prev or nums[i]
    lemma_max_one_of(prev, nums[i]);

    if m == prev {
        // prev is in nums.subrange(0,i) so also in nums.subrange(0,i+1)
        assert(nums.subrange(0, i).contains(prev));
        assert(nums.subrange(0, i + 1).contains(prev));
    } else {
        // m == nums[i], which is in nums.subrange(0,i+1)
        assert(m == nums[i]);
        assert(nums.subrange(0, i + 1).contains(nums[i]));
    }

    // From isMax(prev, nums.subrange(0,i)) we have that all elements in 0..i are <= prev
    assert(isMax(prev, nums.subrange(0, i)));
    assert(forall|k: int| 0 <= k < i ==> nums[k] <= prev);

    // Show prev <= m
    if prev >= nums[i] {
        assert(m == prev);
        assert(prev <= m);
    } else {
        assert(m == nums[i]);
        assert(nums[i] >= prev);
        assert(prev <= m);
    }

    // For k < i: nums[k] <= prev <= m, so nums[k] <= m
    assert(forall|k: int| 0 <= k < i ==> nums[k] <= m);

    // For k == i: nums[i] <= m by definition of m
    assert(nums[i] <= m);

    // Combine for all k < i+1
    assert(forall|k: int| 0 <= k < i + 1 ==> nums[k] <= m);

    // m is contained in the subrange (we already showed one of the two cases)
    assert(nums.subrange(0, i + 1).contains(m));

    // Conclude isMax
    assert(isMax(m, nums.subrange(0, i + 1)));
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<int>) -> (result: Vec<int>)
    requires
        numbers.len() > 0,
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 < i < result.len() ==> isMax(result[i], numbers@.subrange(0, i + 1)),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<int> = Vec::new();
    result.reserve(numbers.len());

    // push first element
    result.push(numbers@[0]);

    // loop over remaining indices 1..numbers.len()-1
    let mut i: int = 1;
    while i < (numbers.len() as int)
        invariant 1 <= i && i <= (numbers.len() as int);
        invariant (result.len() as int) == i;
        invariant forall|j: int| 0 <= j < i ==> isMax(result@[j], numbers@.subrange(0, j + 1));
    {
        let n = numbers@[i];
        let prev = result[(i - 1) as usize];

        if n > prev {
            result.push(n);
            proof {
                // prev isMax for subrange(0,i) by invariant with j = i-1
                assert(isMax(result@[(i - 1)], numbers@.subrange(0, i)));
                // apply lemma_step to conclude isMax(n, subrange(0,i+1))
                lemma_step(i, numbers@, result@[(i - 1)]);
                // lemma_step shows isMax(max_int(prev, numbers[i]), subrange(0,i+1))
                // but since n > prev we have max_int(prev, numbers[i]) == n
                assert(max_int(result@[(i - 1)], numbers@[i]) == numbers@[i]);
                assert(isMax(numbers@[i], numbers@.subrange(0, i + 1)));
            }
        } else {
            result.push(prev);
            proof {
                // prev is already isMax for subrange(0,i). lemma_step shows
                // isMax(max(prev, numbers[i]), subrange(0,i+1)), and here max == prev.
                lemma_step(i, numbers@, result@[(i - 1)]);
                assert(max_int(result@[(i - 1)], numbers@[i]) == result@[(i - 1)]);
                assert(isMax(result@[(i - 1)], numbers@.subrange(0, i + 1)));
            }
        }

        i = i + 1;
    }

    result
}
// </vc-code>

fn main() {
}

}