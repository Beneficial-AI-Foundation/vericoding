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
proof fn seq_max_extends(s: Seq<i32>, last_val: i32, prev_max: i32)
    requires
        s.len() > 0,
        prev_max == seq_max(s.drop_last()),
        last_val == s.last(),
    ensures
        seq_max(s) == if last_val > prev_max { last_val } else { prev_max },
{
    // This follows directly from the definition of seq_max
}

proof fn seq_take_relationship(s: Seq<i32>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.take(i + 1).drop_last() == s.take(i),
        s.take(i + 1).last() == s[i],
{
    assert(s.take(i + 1).len() == i + 1);
    assert(s.take(i + 1).drop_last().len() == i);
    assert forall|j: int| 0 <= j < i ==> s.take(i + 1).drop_last()[j] == s.take(i + 1)[j] by {
        assert(s.take(i + 1).drop_last()[j] == s.take(i + 1)[j]);
    }
    assert forall|j: int| 0 <= j < i ==> s.take(i + 1)[j] == s[j] by {
        assert(s.take(i + 1)[j] == s[j]);
    }
    assert forall|j: int| 0 <= j < i ==> s.take(i)[j] == s[j] by {
        assert(s.take(i)[j] == s[j]);
    }
    assert forall|j: int| 0 <= j < i ==> s.take(i + 1).drop_last()[j] == s.take(i)[j] by {
        assert(s.take(i + 1).drop_last()[j] == s.take(i + 1)[j]);
        assert(s.take(i + 1)[j] == s[j]);
        assert(s.take(i)[j] == s[j]);
    }
    assert(s.take(i + 1).last() == s.take(i + 1)[i]);
    assert(s.take(i + 1)[i] == s[i]);
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
    
    for i in 0..numbers.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1)),
            if i == 0 {
                current_max == i32::MIN
            } else {
                current_max == seq_max(numbers@.take(i as int))
            },
    {
        let val = numbers[i];
        
        if i == 0 {
            current_max = val;
            assert(numbers@.take(1).len() == 1);
            assert(numbers@.take(1)[0] == val);
            assert(seq_max(numbers@.take(1)) == val) by {
                assert(numbers@.take(1).drop_last().len() == 0);
            }
        } else {
            proof {
                seq_take_relationship(numbers@, i as int);
                seq_max_extends(numbers@.take((i + 1) as int), val, current_max);
            }
            if val > current_max {
                current_max = val;
            }
        }
        
        result.push(current_max);
    }
    
    result
}
// </vc-code>

fn main() {}
}