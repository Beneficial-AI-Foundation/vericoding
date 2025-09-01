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
proof fn seq_max_single(a: Seq<i32>)
    requires a.len() == 1,
    ensures seq_max(a) == a[0],
{
    assert(a.drop_last().len() == 0);
    assert(seq_max(a.drop_last()) == i32::MIN);
    assert(a.last() == a[0]);
}

proof fn seq_max_append(a: Seq<i32>, x: i32)
    ensures seq_max(a.push(x)) == if x > seq_max(a) { x } else { seq_max(a) },
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a.push(x).drop_last() == a);
        assert(a.push(x).last() == x);
        assert(seq_max(a) == i32::MIN);
    } else {
        assert(a.push(x).drop_last() == a);
        assert(a.push(x).last() == x);
    }
}

proof fn seq_max_take_relationship(numbers: Seq<i32>, i: int, current_max: i32)
    requires 
        0 <= i < numbers.len(),
        i > 0 ==> current_max == seq_max(numbers.take(i)),
        i == 0 ==> current_max == i32::MIN,
    ensures 
        seq_max(numbers.take(i + 1)) == if numbers[i] > current_max { numbers[i] } else { current_max },
{
    if i == 0 {
        assert(numbers.take(1).len() == 1);
        assert(numbers.take(1) =~= seq![numbers[0]]);
        seq_max_single(numbers.take(1));
        assert(seq_max(numbers.take(1)) == numbers[0]);
        assert(current_max == i32::MIN);
        assert(numbers[0] > i32::MIN);
    } else {
        assert(numbers.take(i + 1) =~= numbers.take(i).push(numbers[i]));
        seq_max_append(numbers.take(i), numbers[i]);
        assert(seq_max(numbers.take(i + 1)) == if numbers[i] > seq_max(numbers.take(i)) { numbers[i] } else { seq_max(numbers.take(i)) });
        assert(current_max == seq_max(numbers.take(i)));
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
    let mut result = Vec::new();
    let mut current_max = i32::MIN;
    let mut i = 0;

    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result.len() == i,
            i > 0 ==> current_max == seq_max(numbers@.take(i as int)),
            i == 0 ==> current_max == i32::MIN,
            forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j + 1)),
        decreases numbers.len() - i,
    {
        let val = numbers[i];
        
        proof {
            seq_max_take_relationship(numbers@, i as int, current_max);
        }
        
        if val > current_max {
            current_max = val;
        }
        
        result.push(current_max);
        
        assert(result[i as int] == current_max);
        assert(current_max == seq_max(numbers@.take(i + 1)));
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}