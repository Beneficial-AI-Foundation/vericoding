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
spec fn max(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

proof fn seq_max_proof(a: Seq<i32>, i: int) 
    requires
        0 <= i <= a.len(),
    ensures
        seq_max(a.take(i)) == if i == 0 { i32::MIN } else { max(a[i as usize - 1], seq_max(a.take(i-1))) },
    decreases i,
{
    if i == 0 {
        assert(seq_max(a.take(0)) == i32::MIN);
    } else {
        seq_max_proof(a, i-1);
        assert(a.take(i).drop_last() == a.take(i-1));
        assert(a.take(i).last() == a[i as usize - 1]);
    }
}

proof fn seq_max_monotonic(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= a.len(),
    ensures
        seq_max(a.take(i)) <= seq_max(a.take(j)),
    decreases j - i,
{
    if i < j {
        seq_max_proof(a, j);
        let prev_max = seq_max(a.take(j-1));
        let current = a[j as usize - 1];
        assert(seq_max(a.take(j)) == max(current, prev_max));
        assert(prev_max <= max(current, prev_max));
        seq_max_monotonic(a, i, j-1);
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
    let mut result: Vec<i32> = Vec::new();
    let mut current_max = i32::MIN;
    let mut idx: usize = 0;
    while idx < numbers.len()
        invariant
            0 <= idx <= numbers.len(),
            result.len() == idx,
            forall|k: int| 0 <= k < idx ==> result[k as usize] == seq_max(numbers@.take(k + 1)),
            current_max == if idx == 0 { i32::MIN } else { seq_max(numbers@.take(idx as int)) },
        decreases numbers.len() - idx,
    {
        let num = numbers[idx];
        proof {
            seq_max_proof(numbers@, idx as int + 1);
        }
        current_max = if num > current_max { num } else { current_max };
        result.push(current_max);
        proof {
            assert(result@.len() == idx + 1);
            assert forall|k: int| 0 <= k < idx implies result[k as usize] == seq_max(numbers@.take(k + 1)) by {
                assert(result[k as usize] == old(result)[k as usize]);
            };
            assert(result[idx] == current_max);
            assert(current_max == max(num, old(current_max)));
            assert(old(current_max) == seq_max(numbers@.take(idx as int)));
            assert(num == numbers@[idx as int]);
            assert(seq_max(numbers@.take(idx as int + 1)) == max(numbers@[idx as int], seq_max(numbers@.take(idx as int))));
        }
        idx = idx + 1;
    }
    result
}
// </vc-code>

fn main() {}
}