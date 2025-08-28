use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// <vc-helpers>
spec fn max_of_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        let sub_max = max_of_seq(s.drop_last());
        if s.last() > sub_max {
            s.last()
        } else {
            sub_max
        }
    }
}

proof fn max_of_seq_is_max(m: int, s: Seq<int>)
    requires
        s.len() > 0,
        m == max_of_seq(s),
    ensures
        isMax(m, s),
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.contains(m));
        assert(forall|i: int| 0 <= i < s.len() ==> s[i] <= m);
    } else {
        let sub_max = max_of_seq(s.drop_last());
        if s.last() > sub_max {
            assert(m == s.last());
            assert(s.contains(m));
            max_of_seq_is_max(sub_max, s.drop_last());
            assert(forall|i: int| 0 <= i < s.len() - 1 ==> s[i] <= sub_max);
            assert(forall|i: int| 0 <= i < s.len() ==> s[i] <= m);
        } else {
            assert(m == sub_max);
            max_of_seq_is_max(sub_max, s.drop_last());
            assert(s.contains(sub_max));
            assert(forall|i: int| 0 <= i < s.len() - 1 ==> s[i] <= sub_max);
            assert(s.last() <= sub_max);
            assert(forall|i: int| 0 <= i < s.len() ==> s[i] <= m);
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn rolling_max(numbers: Vec<int>) -> (result: Vec<int>)
    requires
        numbers.len() > 0,
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 < i < result.len() ==> isMax(result[i], numbers@.subrange(0, i + 1)),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn rolling_max(numbers: Vec<int>) -> (result: Vec<int>)
    requires
        numbers.len() > 0,
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < result.len() ==> isMax(result@[i], numbers@.subrange(0, i + 1)),
{
    let mut result: Vec<int> = Vec::with_capacity(numbers.len());
    result.push(numbers[0]);
    
    let mut i: usize = 1;
    while i < numbers.len()
        invariant
            0 < i <= numbers.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> isMax(result@[j], numbers@.subrange(0, j + 1)),
    {
        let sub_seq = numbers@.subrange(0, i as int + 1);
        let current_max = max_of_seq(sub_seq);
        proof {
            max_of_seq_is_max(current_max, sub_seq);
        }
        result.push(current_max);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}