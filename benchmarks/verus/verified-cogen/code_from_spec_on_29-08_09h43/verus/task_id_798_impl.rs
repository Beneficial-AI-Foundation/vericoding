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
proof fn sum_to_append_lemma(arr: Seq<i64>, val: i64)
    ensures sum_to(arr.push(val)) == sum_to(arr) + val,
    decreases arr.len(),
{
    if arr.len() == 0 {
        assert(arr.push(val).drop_last() == arr);
        assert(arr.push(val).last() == val);
    } else {
        let arr_push = arr.push(val);
        assert(arr_push.drop_last() == arr);
        assert(arr_push.last() == val);
    }
}

proof fn sum_to_prefix_lemma(arr: Seq<i64>, i: nat)
    requires i <= arr.len(),
    ensures sum_to(arr.subrange(0, i as int)) + sum_to(arr.subrange(i as int, arr.len() as int)) == sum_to(arr),
    decreases arr.len(),
{
    if i == arr.len() {
        assert(arr.subrange(0, i as int) == arr);
        assert(arr.subrange(i as int, arr.len() as int).len() == 0);
    } else if i == 0 {
        assert(arr.subrange(0, 0).len() == 0);
        assert(arr.subrange(0, arr.len() as int) == arr);
    } else {
        /* code modified by LLM (iteration 5): use correct inductive structure */
        let prefix = arr.drop_last();
        let last_elem = arr.last();
        sum_to_prefix_lemma(prefix, i);
        
        if i < arr.len() {
            assert(arr.subrange(0, i as int) == prefix.subrange(0, i as int));
            assert(arr.subrange(i as int, arr.len() as int) == 
                   prefix.subrange(i as int, prefix.len() as int).push(last_elem));
        }
    }
}

proof fn sum_to_extend_lemma(arr: Seq<i64>, i: nat)
    requires i < arr.len(),
    ensures sum_to(arr.subrange(0, i as int)) + arr[i as int] == sum_to(arr.subrange(0, (i + 1) as int)),
{
    /* code modified by LLM (iteration 5): fix sequence indexing syntax and prove extension property directly */
    let prefix = arr.subrange(0, i as int);
    let extended = arr.subrange(0, (i + 1) as int);
    assert(extended == prefix.push(arr[i as int]));
    sum_to_append_lemma(prefix, arr[i as int]);
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn sum(arr: &Vec<i64>) -> (sum: i128)
    // post-conditions-start
    ensures
        sum_to(arr@) == sum,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut sum: i128 = 0;
    let mut i = 0;
    
    /* code modified by LLM (iteration 5): fixed loop invariant and added overflow check */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum == sum_to(arr@.subrange(0, i as int)),
            forall|j: int| 0 <= j < i ==> -9223372036854775808i128 <= arr@[j] <= 9223372036854775807i128,
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 5): use helper lemma with correct type conversion */
        proof {
            sum_to_extend_lemma(arr@, i as nat);
        }
        
        sum = sum + (arr[i] as i128);
        i += 1;
    }
    
    /* code modified by LLM (iteration 5): final assertion for postcondition */
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, i as int) == arr@);
    }
    
    sum
}
// </vc-code>

} // verus!

fn main() {}