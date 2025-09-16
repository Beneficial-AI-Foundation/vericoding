// <vc-preamble>
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

spec fn sum_other_way(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + sum_other_way(s.take(s.len() - 1))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma for map over take commutation */
proof fn sum_distributes_over_append(s1: Seq<int>, s2: Seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1 + s2 =~= s2);
    } else {
        assert((s1 + s2)[0] == s1[0]);
        assert((s1 + s2).skip(1) =~= s1.skip(1) + s2);
        sum_distributes_over_append(s1.skip(1), s2);
    }
}

proof fn sum_single_element(x: int)
    ensures sum(seq![x]) == x
{
    assert(seq![x].len() == 1);
    assert(seq![x][0] == x);
    assert(seq![x].skip(1) =~= Seq::<int>::empty());
    assert(sum(seq![x].skip(1)) == 0);
}

proof fn sum_take_next(s: Seq<int>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        sum(s.take(i + 1)) == sum(s.take(i)) + s[i],
    decreases i
{
    assert(s.take(i + 1) =~= s.take(i) + seq![s[i]]);
    sum_distributes_over_append(s.take(i), seq![s[i]]);
    sum_single_element(s[i]);
}

proof fn map_take_commutes(s: Seq<i32>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        s.take(i).map(|_idx, j: i32| j as int) =~= s.map(|_idx, j: i32| j as int).take(i),
{
    assert forall|k: int| 0 <= k < i implies
        s.take(i).map(|_idx, j: i32| j as int)[k] == s.map(|_idx, j: i32| j as int).take(i)[k]
    by {
        assert(s.take(i)[k] == s[k]);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: bool)

    requires
        forall|i: int|
            0 <= i <= operations@.len() ==> sum(operations@.take(i).map(|_idx, j: i32| j as int))
                <= i32::MAX,

    ensures
        result <==> exists|i: int|
            0 <= i <= operations@.len() && sum(operations@.take(i).map(|_idx, j: i32| j as int))
                < 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed sum computation and assertions */
    let mut balance: i64 = 0;
    let mut i: usize = 0;
    
    while i < operations.len()
        invariant
            0 <= i <= operations.len(),
            balance == sum(operations@.take(i as int).map(|_idx, j: i32| j as int)) as i64,
            balance >= i64::MIN,
            balance <= i64::MAX,
            forall|j: int| 0 <= j <= i ==> sum(operations@.take(j).map(|_idx, k: i32| k as int)) >= 0,
        decreases operations.len() - i
    {
        let old_balance = balance;
        let next_val = operations[i] as i64;
        
        // Check for overflow
        if next_val > 0 && balance > i64::MAX - next_val {
            assert(false); // This shouldn't happen due to precondition
        }
        if next_val < 0 && balance < i64::MIN - next_val {
            assert(false); // This shouldn't happen due to precondition  
        }
        
        balance = balance + next_val;
        
        proof {
            map_take_commutes(operations@, (i + 1) as int);
            let mapped_seq = operations@.map(|_idx, j: i32| j as int);
            sum_take_next(mapped_seq, i as int);
            assert(mapped_seq[i as int] == operations@[i as int] as int);
            assert(operations@.take((i + 1) as int).map(|_idx, j: i32| j as int) =~= mapped_seq.take((i + 1) as int));
            assert(sum(operations@.take((i + 1) as int).map(|_idx, j: i32| j as int)) == sum(mapped_seq.take((i + 1) as int)));
            assert(balance == sum(operations@.take((i + 1) as int).map(|_idx, j: i32| j as int)) as i64);
        }
        
        if balance < 0 {
            assert(sum(operations@.take((i + 1) as int).map(|_idx, j: i32| j as int)) < 0);
            assert(exists|j: int| 0 <= j <= operations@.len() && sum(operations@.take(j).map(|_idx, k: i32| k as int)) < 0);
            return true;
        }
        
        i = i + 1;
    }
    
    assert(i == operations.len());
    proof {
        map_take_commutes(operations@, operations@.len() as int);
        assert(operations@.take(operations@.len() as int) =~= operations@);
        assert(balance == sum(operations@.map(|_idx, j: i32| j as int)) as i64);
    }
    
    if balance < 0 {
        assert(sum(operations@.map(|_idx, j: i32| j as int)) < 0);
        assert(sum(operations@.take(operations@.len()).map(|_idx, j: i32| j as int)) < 0);
        return true;
    }
    
    assert(forall|j: int| 0 <= j <= operations.len() ==> sum(operations@.take(j).map(|_idx, k: i32| k as int)) >= 0);
    false
}
// </vc-code>

}
fn main() {}