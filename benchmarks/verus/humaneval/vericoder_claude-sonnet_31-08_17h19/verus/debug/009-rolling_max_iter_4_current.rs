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
proof fn seq_max_monotonic(a: Seq<i32>, b: Seq<i32>)
    requires
        a.len() > 0,
        b.len() > 0,
        a.len() <= b.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] == b[k],
    ensures
        seq_max(a) <= seq_max(b),
    decreases b.len(),
{
    if a.len() == b.len() {
        assert(a =~= b);
    } else {
        if b.last() >= seq_max(b.drop_last()) {
            seq_max_monotonic(a, b.drop_last());
        } else {
            seq_max_monotonic(a, b.drop_last());
        }
    }
}

proof fn seq_max_append_property(a: Seq<i32>, x: i32)
    requires a.len() > 0,
    ensures seq_max(a.push(x)) == if x > seq_max(a) { x } else { seq_max(a) },
{
    let extended = a.push(x);
    assert(extended.last() == x);
    assert(extended.drop_last() =~= a);
}

proof fn seq_max_take_property(a: Seq<i32>, i: int, j: int)
    requires 
        0 < i <= j <= a.len(),
    ensures
        seq_max(a.take(i)) <= seq_max(a.take(j)),
{
    if i == j {
        return;
    }
    seq_max_monotonic(a.take(i), a.take(j));
}

proof fn seq_max_single_element(x: i32)
    ensures seq_max(seq![x]) == x,
{
    let s = seq![x];
    assert(s.len() == 1);
    assert(s.last() == x);
    assert(s.drop_last().len() == 0);
    assert(seq_max(s.drop_last()) == i32::MIN);
    if x == i32::MIN {
        assert(seq_max(s) == x);
    } else {
        assert(x > i32::MIN);
        assert(seq_max(s) == x);
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
    
    for i in 0..numbers.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1)),
    {
        let current_max = if i == 0 {
            numbers[i]
        } else {
            if numbers[i] > result[i - 1] {
                numbers[i]
            } else {
                result[i - 1]
            }
        };
        
        result.push(current_max);
        
        proof {
            assert(numbers@.take((i + 1) as int).last() == numbers[i as int]);
            if i == 0 {
                assert(numbers@.take(1) =~= seq![numbers[0]]);
                seq_max_single_element(numbers[0]);
                assert(seq_max(seq![numbers[0]]) == numbers[0]);
            } else {
                assert(numbers@.take((i + 1) as int) =~= numbers@.take(i as int).push(numbers[i as int]));
                seq_max_append_property(numbers@.take(i as int), numbers[i as int]);
                assert(result[i - 1] == seq_max(numbers@.take(i as int)));
                assert(seq_max(numbers@.take((i + 1) as int)) == 
                    if numbers[i as int] > seq_max(numbers@.take(i as int)) { 
                        numbers[i as int] 
                    } else { 
                        seq_max(numbers@.take(i as int)) 
                    });
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}