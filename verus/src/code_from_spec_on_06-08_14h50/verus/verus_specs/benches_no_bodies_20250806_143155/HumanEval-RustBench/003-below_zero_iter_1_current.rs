use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum(s.skip(1))
    }
}
// pure-end

spec fn sum_other_way(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + sum_other_way(s.take(s.len() - 1))
    }
}
// pure-end

proof fn lemma_sum_equals_sum_other_way(s: Seq<int>)
    // post-conditions-start
    ensures
        sum(s) == sum_other_way(s),
    decreases s.len(),
    // post-conditions-end
{
    // impl-start
    if s.len() == 1 {
        assert(sum(s.skip(1)) == 0);
        assert(sum_other_way(s.take(s.len() - 1)) == 0);
    } else if s.len() > 1 {
        let ss = s.skip(1);
        lemma_sum_equals_sum_other_way(ss);
        assert(sum_other_way(ss) == ss[ss.len() - 1] + sum_other_way(ss.take(ss.len() - 1)));
        lemma_sum_equals_sum_other_way(ss.take(ss.len() - 1));
        assert(ss.take(ss.len() - 1) == s.take(s.len() - 1).skip(1));
        lemma_sum_equals_sum_other_way(s.take(s.len() - 1));
    }
    // impl-end
}
// pure-end

fn below_zero(operations: Vec<i32>) -> (result: bool)
    // pre-conditions-start
    requires
        forall|i: int|
            0 <= i <= operations@.len() ==> sum(operations@.take(i).map(|_idx, j: i32| j as int))
                <= i32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <==> exists|i: int|
            0 <= i <= operations@.len() && sum(operations@.take(i).map(|_idx, j: i32| j as int))
                < 0,
    // post-conditions-end
{
    let mut current_sum: i32 = 0;
    let mut idx: usize = 0;
    
    while idx < operations.len()
        invariant
            0 <= idx <= operations@.len(),
            current_sum == sum(operations@.take(idx as int).map(|_idx, j: i32| j as int)),
            forall|i: int| 0 <= i < idx ==> sum(operations@.take(i).map(|_idx, j: i32| j as int)) >= 0,
    {
        current_sum = current_sum + operations[idx];
        
        if current_sum < 0 {
            assert(sum(operations@.take((idx + 1) as int).map(|_idx, j: i32| j as int)) < 0);
            return true;
        }
        
        idx = idx + 1;
    }
    
    assert(forall|i: int| 0 <= i <= operations@.len() ==> sum(operations@.take(i).map(|_idx, j: i32| j as int)) >= 0);
    false
}

}
fn main() {}