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
        0 <= start <= end < arr.len(),
        start <= i <= end,
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
        let sub1 = arr.subrange(start, i + 1);
        let sub2 = arr.subrange(i + 1, i + 2);
        let sub3 = arr.subrange(i + 2, end + 1);
        assert(arr.subrange(start, i + 2) == sub1 + sub2);
        assert(arr.subrange(i + 1, end + 1) == sub2 + sub3);
        assert(arr.subrange(start, end + 1) == sub1 + sub2 + sub3);
        
        sum_to_additive(sub1, sub2);
        sum_to_additive(sub2, sub3);
        sum_to_additive(sub1 + sub2, sub3);
        
        assert(sum_to(sub1 + sub2) == sum_to(sub1) + sum_to(sub2));
        assert(sum_to(sub2 + sub3) == sum_to(sub2) + sum_to(sub3));
        assert(sum_to(sub1 + sub2 + sub3) == sum_to(sub1 + sub2) + sum_to(sub3));
    }
}

proof fn sum_to_additive(s1: Seq<i64>, s2: Seq<i64>)
    ensures sum_to(s1 + s2) == sum_to(s1) + sum_to(s2),
    decreases s2.len(),
{
    if s2.len() == 0 {
        assert(s1 + s2 == s1);
    } else {
        let s2_init = s2.drop_last();
        let s2_last = s2.last();
        assert(s2 == s2_init.push(s2_last));
        assert(s1 + s2 == (s1 + s2_init).push(s2_last));
        sum_to_additive(s1, s2_init);
        assert(sum_to(s1 + s2_init) == sum_to(s1) + sum_to(s2_init));
        assert(sum_to(s2) == sum_to(s2_init) + s2_last);
        assert(sum_to(s1 + s2) == sum_to(s1 + s2_init) + s2_last);
        assert(sum_to(s1 + s2) == sum_to(s1) + sum_to(s2_init) + s2_last);
        assert(sum_to(s1 + s2) == sum_to(s1) + sum_to(s2));
    }
}

proof fn sum_to_push_lemma(s: Seq<i64>, elem: i64)
    ensures sum_to(s.push(elem)) == sum_to(s) + elem,
{
    assert(s.push(elem).last() == elem);
    assert(s.push(elem).drop_last() == s);
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
    
    /* code modified by LLM (iteration 5): fixed syntax error with sequence indexing */
    while i <= end
        invariant
            start <= i <= end + 1,
            i <= arr.len(),
            sum == sum_to(arr@.subrange(start as int, i as int)),
        decreases end + 1 - i,
    {
        /* code modified by LLM (iteration 5): added bound check and overflow prevention */
        assert(i < arr.len());
        assert(i <= end);
        assert(end < arr.len());
        
        sum = sum + arr[i] as i128;
        
        proof {
            let old_i = i;
            assert(old_i < arr.len());
            assert(start as int <= old_i as int);
            assert(old_i as int < arr@.len());
            assert(0 <= start as int <= old_i as int < arr@.len());
            assert(0 <= start as int <= (old_i + 1) as int <= arr@.len());
            
            sum_to_push_lemma(arr@.subrange(start as int, old_i as int), arr@[old_i as int]);
            
            assert(arr@.subrange(start as int, (old_i + 1) as int) == 
                   arr@.subrange(start as int, old_i as int).push(arr@[old_i as int]));
            assert(sum_to(arr@.subrange(start as int, (old_i + 1) as int)) == 
                   sum_to(arr@.subrange(start as int, old_i as int)) + arr@[old_i as int]);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == end + 1);
        assert(sum == sum_to(arr@.subrange(start as int, (end + 1) as int)));
    }
    
    sum
}
// </vc-code>

} // verus!

fn main() {}