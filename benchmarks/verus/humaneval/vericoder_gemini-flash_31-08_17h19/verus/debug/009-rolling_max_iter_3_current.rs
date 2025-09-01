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
#[verifier(external_body)]
#[allow(unused_mut)]
pub fn vec_pop<T>(vec: &mut Vec<T>) -> T {
    vec.pop().unwrap()
}

#[verifier(external_body)]
pub fn vec_push<T>(vec: &mut Vec<T>, value: T) {
    vec.push(value);
}

spec fn max_val(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
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
    let mut current_max: i32 = i32::MIN;

    if numbers.len() == 0 {
        return Vec::new();
    }

    let mut i: nat = 0; // Changed to nat
    while (i as int) < numbers.len() // Cast i to int for comparison
        invariant
            i as int >= 0,
            i as int <= numbers.len(),
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result[j] == seq_max(numbers@.take(j + 1)),
            current_max == seq_max(numbers@.take(i as int)),
    {
        let num_i = numbers@[i as int];
        current_max = max_val(current_max, num_i);
        vec_push(&mut result, current_max);

        proof {
            assert(current_max == seq_max(numbers@.take(i as int + 1))) by {
                let s_prev = numbers@.take(i as int);
                let s_current = numbers@.take(i as int + 1);
                assert(s_current.len() == i as int + 1);
                assert(s_current.drop_last() =~= s_prev);
                assert(s_current.last() == num_i);

                if s_prev.len() == 0 {
                    // This case is only for i=0
                    assert(s_prev.len() == 0);
                    assert(seq_max(s_prev) == i32::MIN);
                    assert(current_max == max_val(i32::MIN, num_i));
                    assert(seq_max(s_current) == max_val(seq_max(s_prev), s_current.last()));
                    assert(seq_max(s_current) == max_val(i32::MIN, num_i));
                } else {
                    assert(current_max == max_val(seq_max(s_prev), num_i));
                    assert(seq_max(s_current) == max_val(seq_max(s_prev), s_current.last()));
                }
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}