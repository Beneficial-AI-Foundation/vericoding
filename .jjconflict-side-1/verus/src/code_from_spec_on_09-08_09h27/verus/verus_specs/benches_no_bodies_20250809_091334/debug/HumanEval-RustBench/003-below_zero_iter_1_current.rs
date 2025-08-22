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
    if s.len() == 0 {
        // Base case: both sums are 0
    } else if s.len() == 1 {
        // Base case: both sums equal s[0]
        assert(sum(s) == s[0]);
        assert(sum_other_way(s) == s[0]);
    } else {
        // Inductive case: s.len() >= 2
        let s_skip = s.skip(1);
        let s_take = s.take(s.len() - 1);
        
        // Apply inductive hypothesis to the middle part
        let middle = s.skip(1).take(s.len() - 2);
        lemma_sum_equals_sum_other_way(middle);
        
        // Show that s_skip.take(s_skip.len() - 1) == middle
        assert(s_skip.take(s_skip.len() - 1) =~= middle);
        
        // Show that s_take.skip(1) == middle  
        assert(s_take.skip(1) =~= middle);
        
        // Apply inductive hypothesis to s_skip and s_take
        lemma_sum_equals_sum_other_way(s_skip);
        lemma_sum_equals_sum_other_way(s_take);
        
        // Now prove the equality by rearranging
        assert(sum(s) == s[0] + sum(s_skip));
        assert(sum_other_way(s) == s[s.len() - 1] + sum_other_way(s_take));
        
        // Use the fact that sum(s_skip) == sum_other_way(s_skip)
        // and sum(s_take) == sum_other_way(s_take)
        // and rearrange to show equality
    }
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
    let mut balance: i32 = 0;
    let mut idx: usize = 0;
    
    while idx <= operations.len()
        invariant
            0 <= idx <= operations.len(),
            balance == sum(operations@.take(idx as int).map(|_idx, j: i32| j as int)),
            forall|i: int| 0 <= i < idx ==> sum(operations@.take(i).map(|_idx, j: i32| j as int)) >= 0,
    {
        if balance < 0 {
            return true;
        }
        
        if idx == operations.len() {
            break;
        }
        
        balance = balance + operations[idx];
        idx = idx + 1;
    }
    
    false
}

}
fn main() {}