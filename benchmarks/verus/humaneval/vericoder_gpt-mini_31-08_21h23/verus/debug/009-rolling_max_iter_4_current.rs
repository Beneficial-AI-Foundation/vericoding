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
proof fn seq_take_last_drop(numbers: Vec<i32>, i: nat)
    ensures numbers@.take(i + 1).last() == numbers@[i as int]
    ensures numbers@.take(i + 1).drop_last() == numbers@.take(i)
    decreases i
{
    if i == 0 {
        // take(1) has length 1 and its only element is numbers@[0]
        assert(numbers@.take(1).len() == 1);
        assert(numbers@.take(1).last() == numbers@[0]);
        assert(numbers@.take(1).drop_last() == numbers@.take(0));
    } else {
        // For i > 0, by definition of take:
        // the last element of take(i+1) is numbers@[i]
        // and dropping the last returns take(i)
        assert(numbers@.take(i + 1).len() == i + 1);
        assert(numbers@.take(i + 1).last() == numbers@[i as int]);
        assert(numbers@.take(i + 1).drop_last() == numbers@.take(i));
    }
}

proof fn lemma_take_seq_max(numbers: Vec<i32>, i: nat)
    ensures seq_max(numbers@.take(i + 1)) == if numbers@[i as int] > seq_max(numbers@.take(i)) { numbers@[i as int] } else { seq_max(numbers@.take(i)) }
    decreases i
{
    seq_take_last_drop(numbers, i);
    // Unfold seq_max for non-empty sequence take(i+1)
    assert(seq_max(numbers@.take(i + 1)) ==
           if numbers@.take(i + 1).last() > seq_max(numbers@.take(i + 1).drop_last()) {
               numbers@.take(i + 1).last()
           } else {
               seq_max(numbers@.take(i + 1).drop_last())
           });
    assert(numbers@.take(i + 1).last() == numbers@[i as int]);
    assert(numbers@.take(i + 1).drop_last() == numbers@.take(i));
    assert(seq_max(numbers@.take(i + 1)) ==
           if numbers@[i as int] > seq_max(numbers@.take(i)) {
               numbers@[i as int]
           } else {
               seq_max(numbers@.take(i))
           });
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
        let old_cur = cur_max;
        let v = numbers[i as usize];
        if v > cur_max {
            cur_max = v;
        }
        // cur_max is now the max of old_cur and v
        assert(cur_max == if v > old_cur { v } else { old_cur });
        // old_cur equals seq_max(numbers@.take(i)) by the loop invariant
        assert(old_cur == seq_max(numbers@.take(i)));
        // relate the seq_max of take(i+1) to the new element
        lemma_take_seq_max(numbers, i);
        // relate the runtime v to the specification sequence element
        assert(numbers@[i as int] == v);
        // combine to get cur_max == seq_max(numbers@.take(i+1))
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