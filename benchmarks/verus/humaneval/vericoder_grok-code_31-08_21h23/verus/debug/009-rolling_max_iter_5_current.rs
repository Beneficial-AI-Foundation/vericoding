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
// </vc-helpers>
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
    let len = numbers.len();
    proof {
        assert((numbers@).take(0).len() == 0);
        assert(seq_max((numbers@).take(0)) == i32::MIN);
    }
    result = Vec::with_capacity(len);
    current_max = i32::MIN;
    let mut i = 0;
    while i < len
        invariant
            0 <= i as int <= len as int,
            result.len() == i,
            current_max == if i == 0 { i32::MIN } else { seq_max((numbers@).take(i as int)) },
            forall|j: int| 0 <= j < i as int ==> result@[j] == seq_max((numbers@).take(j + 1)) as i32
        decreases (len - i)
    {
        if numbers[i] > current_max {
            current_max = numbers[i];
        }
        proof {
            assert(current_max == seq_max((numbers@).take(i as int + 1)));
        }
        result.push(current_max);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}