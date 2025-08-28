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
proof fn lemma_sum_to_empty()
    ensures sum_to(Seq::<i64>::empty()) == 0
{
}

proof fn lemma_sum_to_single(x: i64)
    ensures sum_to(seq![x]) == x
{
    assert(seq![x].len() == 1);
    assert(seq![x].drop_last() == Seq::<i64>::empty());
    assert(seq![x].last() == x);
    lemma_sum_to_empty();
}

proof fn lemma_sum_to_push(arr: Seq<i64>, x: i64)
    ensures sum_to(arr.push(x)) == sum_to(arr) + x
    decreases arr.len()
{
    if arr.len() == 0 {
        lemma_sum_to_empty();
        lemma_sum_to_single(x);
        assert(arr.push(x) == seq![x]);
    } else {
        assert(arr.push(x).last() == x);
        lemma_sum_to_push(arr.drop_last(), x);
    }
}

proof fn lemma_sum_to_prefix(arr: Seq<i64>, i: nat)
    requires i <= arr.len()
    ensures sum_to(arr.subrange(0, i as int)) == sum_to(arr.take(i as int))
{
}

proof fn lemma_take_push_relationship(arr: Seq<i64>, i: nat)
    requires i < arr.len()
    ensures arr.take((i + 1) as int) == arr.take(i as int).push(arr[i as int])
{
}
// </vc-helpers>

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
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant 
            i <= arr.len(),
            sum == sum_to(arr@.take(i as int)),
            sum >= i128::MIN / 2 && sum <= i128::MAX / 2,
            forall|j: int| 0 <= j < i ==> arr@[j] >= i128::MIN / 2 && arr@[j] <= i128::MAX / 2
        decreases arr.len() - i
    {
        proof {
            lemma_take_push_relationship(arr@, i);
            lemma_sum_to_push(arr@.take(i as int), arr@[i as int]);
        }
        
        sum = sum + arr[i] as i128;
        i = i + 1;
    }
    
    proof {
        assert(arr@.take(arr.len() as int) == arr@);
    }
    
    sum
}
// </vc-code>

} // verus!

fn main() {}