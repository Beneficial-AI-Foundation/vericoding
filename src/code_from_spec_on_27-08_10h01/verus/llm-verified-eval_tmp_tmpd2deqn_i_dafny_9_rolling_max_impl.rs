use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// <vc-helpers>
spec fn max_of_seq(s: Seq<int>) -> int 
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest_max = max_of_seq(s.subrange(1, s.len() as int));
        if s[0] >= rest_max { s[0] } else { rest_max }
    }
}

proof fn max_of_seq_is_max(s: Seq<int>)
    requires s.len() > 0
    ensures isMax(max_of_seq(s), s)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.contains(s[0]));
        assert(forall|i: int| 0 <= i < s.len() ==> s[i] <= s[0]);
    } else {
        let rest = s.subrange(1, s.len() as int);
        max_of_seq_is_max(rest);
        let rest_max = max_of_seq(rest);
        let m = max_of_seq(s);
        
        if s[0] >= rest_max {
            assert(m == s[0]);
            assert(s.contains(m));
            assert(forall|i: int| 0 <= i < s.len() ==> s[i] <= m) by {
                assert(forall|i: int| 1 <= i < s.len() ==> s[i] <= rest_max);
                assert(forall|i: int| 1 <= i < s.len() ==> s[i] <= s[0]);
            }
        } else {
            assert(m == rest_max);
            assert(rest.contains(rest_max));
            assert(s.contains(m));
            assert(forall|i: int| 0 <= i < s.len() ==> s[i] <= m) by {
                assert(forall|i: int| 1 <= i < s.len() ==> s[i] <= rest_max);
                assert(s[0] < rest_max);
            }
        }
    }
}

proof fn subrange_contains(s: Seq<int>, start: int, end: int, x: int)
    requires 
        0 <= start <= end <= s.len(),
        s.subrange(start, end).contains(x)
    ensures s.contains(x)
{
}

proof fn max_of_seq_in_subrange(s: Seq<int>, start: int, end: int)
    requires 0 <= start < end <= s.len()
    ensures max_of_seq(s.subrange(start, end)) == max_of_seq(s.subrange(start, end))
{
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
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            result.len() == i,
            forall|j: int| 0 < j < i ==> isMax(result@[j], numbers@.subrange(0, j + 1)),
    {
        let current_max = if i == 0 {
            numbers[0]
        } else {
            let prev_max = result[i - 1];
            if numbers[i] > prev_max { numbers[i] } else { prev_max }
        };
        
        result.push(current_max);
        
        proof {
            if i > 0 {
                let subseq = numbers@.subrange(0, i as int + 1);
                let prev_subseq = numbers@.subrange(0, i as int);
                
                assert(subseq[i as int] == numbers[i as int]);
                assert(subseq.subrange(0, i as int) == prev_subseq);
                
                if numbers[i as int] > result@[i - 1] {
                    assert(current_max == numbers[i as int]);
                    assert(subseq.contains(current_max));
                    assert(forall|k: int| 0 <= k < subseq.len() ==> subseq[k] <= current_max) by {
                        assert(forall|k: int| 0 <= k < i as int ==> subseq[k] <= result@[i - 1]);
                        assert(forall|k: int| 0 <= k < i as int ==> subseq[k] < numbers[i as int]);
                        assert(subseq[i as int] == numbers[i as int]);
                    }
                } else {
                    assert(current_max == result@[i - 1]);
                    assert(isMax(result@[i - 1], prev_subseq));
                    assert(prev_subseq.contains(result@[i - 1]));
                    assert(subseq.contains(current_max));
                    assert(forall|k: int| 0 <= k < subseq.len() ==> subseq[k] <= current_max) by {
                        assert(forall|k: int| 0 <= k < i as int ==> subseq[k] <= result@[i - 1]);
                        assert(subseq[i as int] == numbers[i as int]);
                        assert(numbers[i as int] <= result@[i - 1]);
                    }
                }
                assert(isMax(current_max, subseq));
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}