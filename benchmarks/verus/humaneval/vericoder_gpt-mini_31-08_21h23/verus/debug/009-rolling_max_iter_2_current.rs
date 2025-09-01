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
// No helpers needed for this proof.
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
    let mut i: nat = 0;
    let mut cur_max: i32 = i32::MIN;
    while i < (numbers.len() as nat)
        invariant
            i <= (numbers.len() as nat),
            (result.len() as nat) == i,
            cur_max == seq_max(numbers@.take(i)),
            forall |k: int| 0 <= k && k < (i as int) ==> result[k] == seq_max(numbers@.take((k + 1) as nat)),
        decreases (numbers.len() as nat) - i
    {
        let v = numbers[i as usize];
        if v > cur_max {
            cur_max = v;
        }
        assert(cur_max == seq_max(numbers@.take(i + 1)));
        result.push(cur_max);
        i = i + 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}