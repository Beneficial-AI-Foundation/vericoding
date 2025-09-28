// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(arr: Seq<i64>) -> (result: int)
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed assert forall syntax with by block */
proof fn sum_to_append(arr: Seq<i64>, x: i64)
    ensures sum_to(arr.push(x)) == sum_to(arr) + x
    decreases arr.len()
{
    assert(arr.push(x).drop_last() == arr);
    assert(arr.push(x).last() == x);
}

proof fn take_push_lemma(arr: Seq<i64>, i: int)
    requires 0 <= i < arr.len()
    ensures arr.take(i + 1) == arr.take(i).push(arr[i])
{
    assert(arr.take(i + 1).len() == i + 1);
    assert(arr.take(i).len() == i);
    assert forall|j: int| 0 <= j < i ==> arr.take(i + 1)[j] == arr[j] by {
        assert(arr.take(i + 1)[j] == arr[j]);
    }
    assert forall|j: int| 0 <= j < i ==> arr.take(i)[j] == arr[j] by {
        assert(arr.take(i)[j] == arr[j]);
    }
    assert(arr.take(i + 1)[i] == arr[i]);
}
// </vc-helpers>

// <vc-spec>
fn sum(arr: &Vec<i64>) -> (result: i128)

    ensures
        sum_to(arr@) == result
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed */
    let mut total: i128 = 0;
    let mut i: usize = 0;
    let n = arr.len();
    
    while i < n
        invariant
            i <= n,
            n == arr.len(),
            total == sum_to(arr@.take(i as int)),
            forall|j: int| 0 <= j < i ==> i64::MIN <= arr@[j] <= i64::MAX,
        decreases n - i
    {
        let old_total = total;
        let arr_i = arr[i] as i128;
        
        proof {
            take_push_lemma(arr@, i as int);
            sum_to_append(arr@.take(i as int), arr@[i as int]);
            assert(arr@.take((i + 1) as int) == arr@.take(i as int).push(arr@[i as int]));
            assert(sum_to(arr@.take((i + 1) as int)) == sum_to(arr@.take(i as int)) + arr@[i as int]);
        }
        
        total = total + arr_i;
        i = i + 1;
        
        assert(total == old_total + arr_i);
        assert(total == sum_to(arr@.take(i as int)));
    }
    
    assert(arr@.take(n as int) == arr@);
    total
}
// </vc-code>

}
fn main() {}