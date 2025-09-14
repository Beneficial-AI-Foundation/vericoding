// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn seq_max(a: Seq<i32>) -> i32
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
// </vc-preamble>

// <vc-helpers>
proof fn seq_max_property(s: Seq<i32>, i: int)
    requires 0 <= i < s.len()
    ensures seq_max(s.take(i + 1)) == if i == 0 { s[0] } else if s[i] > seq_max(s.take(i)) { s[i] } else { seq_max(s.take(i)) }
    decreases i
{
    if i == 0 {
        assert(s.take(1).len() == 1);
        assert(s.take(1).last() == s[0]);
        assert(s.take(1).drop_last().len() == 0);
        assert(seq_max(s.take(1).drop_last()) == i32::MIN);
        assert(seq_max(s.take(1)) == if s.take(1).last() > i32::MIN { s.take(1).last() } else { i32::MIN });
        assert(seq_max(s.take(1)) == s[0]);
    } else {
        assert(s.take(i + 1).len() == i + 1);
        assert(s.take(i + 1).last() == s[i]);
        assert(s.take(i + 1).drop_last() =~= s.take(i));
        assert(seq_max(s.take(i + 1)) == if s[i] > seq_max(s.take(i)) { s[i] } else { seq_max(s.take(i)) });
    }
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed assertion by proving seq_max(s.take(1)) == s[0] correctly */
    let mut result = Vec::new();
    let mut max_so_far = i32::MIN;
    
    for i in 0..numbers.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1)),
            if i == 0 { max_so_far == i32::MIN } else { max_so_far == seq_max(numbers@.take(i as int)) },
    {
        if i == 0 {
            max_so_far = numbers[i];
        } else {
            if numbers[i] > max_so_far {
                max_so_far = numbers[i];
            }
        }
        
        proof {
            seq_max_property(numbers@, i as int);
            if i == 0 {
                assert(numbers@.take(1).len() == 1);
                assert(numbers@.take(1).last() == numbers@[0]);
                assert(numbers@.take(1).drop_last().len() == 0);
                assert(seq_max(numbers@.take(1).drop_last()) == i32::MIN);
                assert(seq_max(numbers@.take(1)) == numbers@[0]);
            } else {
                assert(max_so_far == if numbers@[i as int] > seq_max(numbers@.take(i as int)) { numbers@[i as int] } else { seq_max(numbers@.take(i as int)) });
                assert(max_so_far == seq_max(numbers@.take(i as int + 1)));
            }
        }
        
        result.push(max_so_far);
    }
    
    result
}
// </vc-code>

}
fn main() {}