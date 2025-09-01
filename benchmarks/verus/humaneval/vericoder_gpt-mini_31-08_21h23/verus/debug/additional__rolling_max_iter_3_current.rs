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
proof fn lemma_seq_max_take_succ(s: Seq<i32>, n: nat)
    requires n < s.len()
    ensures seq_max(s.take(n + 1)) == std::cmp::max(seq_max(s.take(n)), s@[n])
    decreases n
{
    if n == 0 {
        assert(s.take(1).drop_last() == s.take(0));
        assert(s.take(1).last() == s@[0]);
        if s.take(1).last() > seq_max(s.take(1).drop_last()) {
            assert(seq_max(s.take(1)) == s.take(1).last());
        } else {
            assert(seq_max(s.take(1)) == seq_max(s.take(1).drop_last()));
        }
        assert(seq_max(s.take(0)) == i32::MIN);
        assert(std::cmp::max(seq_max(s.take(0)), s@[0]) == s@[0]);
    } else {
        assert(s.take(n + 1).drop_last() == s.take(n));
        assert(s.take(n + 1).last() == s@[n]);
        if s.take(n + 1).last() > seq_max(s.take(n + 1).drop_last()) {
            assert(seq_max(s.take(n + 1)) == s.take(n + 1).last());
        } else {
            assert(seq_max(s.take(n + 1)) == seq_max(s.take(n + 1).drop_last()));
        }
        assert(seq_max(s.take(n + 1)) == std::cmp::max(seq_max(s.take(n)), s@[n]));
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
    let mut i: nat = 0;
    let len: nat = numbers.len();
    while i < len
        invariant i <= len
        invariant result.len() == i
        invariant forall |j: nat| j < i ==> result[j] == seq_max(numbers@.take(j + 1))
    {
        let val: i32 = numbers[i];
        let prev_seq: i32 = if i == 0 { i32::MIN } else { result[i - 1] };
        let new_max: i32 = std::cmp::max(prev_seq, val);

        proof {
            if i == 0 {
                assert(prev_seq == seq_max(numbers@.take(0)));
            } else {
                let j: nat = i - 1;
                assert(result[j] == seq_max(numbers@.take(j + 1)));
                assert(prev_seq == seq_max(numbers@.take(i)));
            }
            lemma_seq_max_take_succ(numbers@, i);
            assert(new_max == seq_max(numbers@.take(i + 1)));
        }

        result.push(new_max);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}