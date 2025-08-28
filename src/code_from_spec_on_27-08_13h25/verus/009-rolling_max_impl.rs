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
// pure-end

// <vc-helpers>
proof fn seq_max_leq_elements(a: Seq<i32>)
    requires a.len() > 0,
    ensures forall|i: int| 0 <= i < a.len() ==> a[i] <= seq_max(a),
    decreases a.len(),
{
    if a.len() == 1 {
        assert(a[0] == seq_max(a));
    } else {
        seq_max_leq_elements(a.drop_last());
        if a.last() > seq_max(a.drop_last()) {
            assert(forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= seq_max(a.drop_last()));
            assert(a.last() > seq_max(a.drop_last()));
            assert(forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= a.last());
        } else {
            assert(forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= seq_max(a.drop_last()));
            assert(seq_max(a.drop_last()) == seq_max(a));
        }
        assert(a.last() <= seq_max(a));
    }
}

proof fn seq_max_take_leq_seq_max(a: Seq<i32>, n: int)
    requires 0 < n <= a.len(),
    ensures seq_max(a.take(n)) <= seq_max(a),
    decreases n,
{
    seq_max_leq_elements(a);
    assert(forall|i: int| 0 <= i < n ==> a.take(n)[i] == a[i]);
    assert(forall|i: int| 0 <= i < n ==> a[i] <= seq_max(a));
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
    let mut result = Vec::new();
    let mut current_max = i32::MIN;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k as usize] == seq_max(numbers@.take(k + 1)),
            current_max == if i == 0 { i32::MIN } else { seq_max(numbers@.take(i as int)) },
        decreases numbers.len() - i,
    {
        if numbers.len() > 0 {
            if i == 0 {
                current_max = numbers[0];
            } else if numbers[i as usize] > current_max {
                current_max = numbers[i as usize];
            } else {
                current_max = current_max;
            }
            proof {
                if i > 0 {
                    seq_max_take_leq_seq_max(numbers@, i as int);
                    assert(seq_max(numbers@.take(i as int)) <= seq_max(numbers@.take((i + 1) as int)));
                    if numbers[i as usize] > current_max {
                        assert(numbers[i as usize] == seq_max(numbers@.take((i + 1) as int)));
                    } else {
                        assert(current_max == seq_max(numbers@.take(i as int)));
                        assert(current_max >= numbers[i as usize]);
                        assert(current_max == seq_max(numbers@.take((i + 1) as int)));
                    }
                } else {
                    assert(current_max == numbers[0]);
                    assert(seq_max(numbers@.take(1)) == numbers[0]);
                }
            }
            result.push(current_max);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}