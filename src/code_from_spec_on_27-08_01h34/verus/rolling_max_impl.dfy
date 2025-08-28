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
proof fn seq_max_properties(a: Seq<i32>)
    ensures
        a.len() > 0 ==> (forall|i: int| 0 <= i < a.len() ==> a[i] <= seq_max(a)),
        a.len() > 0 ==> (exists|i: int| 0 <= i < a.len() && a[i] == seq_max(a)),
    decreases a.len(),
{
    if a.len() > 0 {
        if a.len() == 1 {
            assert(a == seq![a[0]]);
            assert(seq_max(a) == a[0]);
        } else {
            seq_max_properties(a.drop_last());
            let last_elem = a.last();
            let rest_max = seq_max(a.drop_last());
            let full_max = seq_max(a);
            
            if last_elem > rest_max {
                assert(full_max == last_elem);
                assert(forall|i: int| 0 <= i < a.len() - 1 ==> a[i] == a.drop_last()[i]);
                assert(forall|i: int| 0 <= i < a.len() - 1 ==> a.drop_last()[i] <= rest_max);
                assert(forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= rest_max);
                assert(rest_max < last_elem);
                assert(a[a.len() - 1] == last_elem);
            } else {
                assert(full_max == rest_max);
                assert(exists|i: int| 0 <= i < a.len() - 1 && a[i] == rest_max);
            }
        }
    }
}

proof fn seq_max_prefix_monotonic(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j < a.len(),
    ensures
        seq_max(a.take(i + 1)) <= seq_max(a.take(j + 1)),
    decreases j - i,
{
    if i == j {
        return;
    }
    
    seq_max_prefix_monotonic(a, i, j - 1);
    
    let prefix_j = a.take(j + 1);
    let prefix_j_minus_1 = a.take(j);
    
    assert(prefix_j_minus_1 == prefix_j.drop_last());
    assert(prefix_j.last() == a[j]);
}

proof fn seq_max_take_properties(a: Seq<i32>, k: int)
    requires 0 < k <= a.len()
    ensures
        k == 1 ==> seq_max(a.take(k)) == a[0],
        k > 1 ==> seq_max(a.take(k)) == if a[k-1] > seq_max(a.take(k-1)) { a[k-1] } else { seq_max(a.take(k-1)) },
{
    if k == 1 {
        assert(a.take(1) == seq![a[0]]);
        assert(a.take(1).len() == 1);
        assert(seq_max(a.take(1)) == a.take(1)[0]);
        assert(a.take(1)[0] == a[0]);
    } else {
        let prefix_k = a.take(k);
        let prefix_k_minus_1 = a.take(k - 1);
        assert(prefix_k.drop_last() == prefix_k_minus_1);
        assert(prefix_k.last() == a[k-1]);
        assert(seq_max(prefix_k) == if prefix_k.last() > seq_max(prefix_k.drop_last()) { prefix_k.last() } else { seq_max(prefix_k.drop_last()) });
        assert(seq_max(prefix_k) == if a[k-1] > seq_max(prefix_k_minus_1) { a[k-1] } else { seq_max(prefix_k_minus_1) });
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
            result.len() == i,
            i <= numbers.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == seq_max(numbers@.take(j + 1)),
            i > 0 ==> current_max == seq_max(numbers@.take(i as int)),
        decreases numbers.len() - i
    {
        if i == 0 {
            current_max = numbers[0];
            proof {
                seq_max_take_properties(numbers@, 1);
            }
        } else {
            if numbers[i] > current_max {
                current_max = numbers[i];
            }
            proof {
                seq_max_take_properties(numbers@, (i + 1) as int);
                assert(numbers@[i as int] == numbers[i]);
                assert(current_max == seq_max(numbers@.take(i as int)));
                
                if numbers[i] > current_max {
                    assert(numbers@[i as int] > seq_max(numbers@.take(i as int)));
                    assert(seq_max(numbers@.take((i + 1) as int)) == numbers@[i as int]);
                    assert(current_max == numbers[i]);
                } else {
                    assert(numbers@[i as int] <= seq_max(numbers@.take(i as int)));
                    assert(seq_max(numbers@.take((i + 1) as int)) == seq_max(numbers@.take(i as int)));
                }
            }
        }
        
        result.push(current_max);
        
        proof {
            assert(result@[i as int] == current_max);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}