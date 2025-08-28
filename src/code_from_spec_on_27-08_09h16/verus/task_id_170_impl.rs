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
// pure-end

// <vc-helpers>
proof fn sum_to_subrange_lemma(arr: Seq<i64>, start: int, end: int, i: int)
    requires
        0 <= start <= i <= end < arr.len(),
    ensures
        sum_to(arr.subrange(start, i + 1)) + sum_to(arr.subrange(i + 1, end + 1)) == sum_to(arr.subrange(start, end + 1)),
    decreases end - i,
{
    if i == end {
        assert(arr.subrange(i + 1, end + 1) == Seq::<i64>::empty());
        assert(sum_to(arr.subrange(i + 1, end + 1)) == 0);
        assert(arr.subrange(start, i + 1) == arr.subrange(start, end + 1));
    } else {
        sum_to_subrange_lemma(arr, start, end, i + 1);
        assert(arr.subrange(start, i + 2) == arr.subrange(start, i + 1).push(arr[i + 1]));
        sum_to_push_lemma(arr.subrange(start, i + 1), arr[i + 1]);
        assert(sum_to(arr.subrange(start, i + 2)) == sum_to(arr.subrange(start, i + 1)) + arr[i + 1]);
    }
}

proof fn sum_to_push_lemma(s: Seq<i64>, x: i64)
    ensures
        sum_to(s.push(x)) == sum_to(s) + x,
{
    assert(s.push(x).drop_last() == s);
    assert(s.push(x).last() == x);
}
// </vc-helpers>

// <vc-spec>
fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)
    // pre-conditions-start
    requires
        0 <= start <= end,
        start <= end < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut sum: i128 = 0;
    let mut i = start;
    
    while i <= end
        invariant
            start <= i <= end + 1,
            i <= arr.len(),
            sum == sum_to(arr@.subrange(start as int, i as int)),
        decreases end + 1 - i,
    {
        sum = sum + arr[i] as i128;
        
        proof {
            assert(arr@.subrange(start as int, (i + 1) as int) == 
                   arr@.subrange(start as int, i as int).push(arr@[i as int]));
            sum_to_push_lemma(arr@.subrange(start as int, i as int), arr@[i as int]);
        }
        
        i = i + 1;
    }
    
    sum
}
// </vc-code>

} // verus!

fn main() {}