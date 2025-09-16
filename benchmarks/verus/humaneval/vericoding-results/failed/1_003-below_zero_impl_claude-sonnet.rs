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
/* helper modified by LLM (iteration 5): fixed lemma proofs and added balance conversion lemma */
proof fn sum_take_property(s: Seq<int>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        sum(s.take(i)) == if i == 0 { 0 } else { sum(s.take(i - 1)) + s[i - 1] },
{
    if i == 0 {
        return;
    }
    if i == 1 {
        assert(s.take(1) == seq![s[0]]);
        assert(sum(s.take(1)) == s[0]);
        assert(sum(s.take(0)) == 0);
        return;
    }
    let take_i = s.take(i);
    let take_i_minus_1 = s.take(i - 1);
    assert(take_i == seq![s[0]] + take_i_minus_1.skip(0));
    assert(sum(take_i) == s[0] + sum(take_i.skip(1)));
    assert(take_i.skip(1) == s.skip(1).take(i - 1));
    sum_take_property(s.skip(1), i - 1);
    assert(sum(s.skip(1).take(i - 1)) == sum(s.take(i - 1).skip(1)) + s[i - 1]);
    assert(sum(s.take(i - 1).skip(1)) == sum(s.take(i - 1)) - s[0]);
}

proof fn balance_conversion_lemma(operations: Vec<i32>, balance: i32, i: usize)
    requires
        0 <= i <= operations.len(),
        balance == sum(operations@.take(i as int).map(|_idx, j: i32| j as int)),
        balance as int <= i32::MAX,
        balance as int >= i32::MIN,
        i < operations.len(),
        forall|k: int| 0 <= k <= operations@.len() ==> sum(operations@.take(k).map(|_idx, j: i32| j as int)) <= i32::MAX,
    ensures
        (balance + operations[i]) as int == sum(operations@.take((i + 1) as int).map(|_idx, j: i32| j as int)),
{
    let seq_ops = operations@.map(|_idx, j: i32| j as int);
    sum_take_property(seq_ops, (i + 1) as int);
    assert(sum(seq_ops.take((i + 1) as int)) == sum(seq_ops.take(i as int)) + seq_ops[i as int]);
    assert(seq_ops[i as int] == operations[i] as int);
    assert(balance as int + operations[i] as int == (balance + operations[i]) as int);
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
    /* code modified by LLM (iteration 5): fixed overflow handling and proof assertions */
    let mut balance = 0i32;
    let mut i = 0;
    
    while i < operations.len()
        invariant
            0 <= i <= operations.len(),
            balance as int == sum(operations@.take(i as int).map(|_idx, j: i32| j as int)),
            forall|k: int| 0 <= k < i ==> sum(operations@.take(k).map(|_idx, j: i32| j as int)) >= 0,
            balance as int >= i32::MIN,
            balance as int <= i32::MAX,
        decreases operations.len() - i,
    {
        proof {
            assert(i < operations.len());
            assert(sum(operations@.take(i as int).map(|_idx, j: i32| j as int)) <= i32::MAX);
            assert(operations[i] as int >= i32::MIN && operations[i] as int <= i32::MAX);
            balance_conversion_lemma(operations, balance, i);
        }
        
        balance = balance + operations[i];
        
        if balance < 0 {
            proof {
                assert(balance as int < 0);
                assert(balance as int == sum(operations@.take((i + 1) as int).map(|_idx, j: i32| j as int)));
                assert(exists|k: int| 0 <= k <= operations@.len() && sum(operations@.take(k).map(|_idx, j: i32| j as int)) < 0);
            }
            return true;
        }
        
        proof {
            assert(balance as int >= 0);
            assert(sum(operations@.take((i + 1) as int).map(|_idx, j: i32| j as int)) >= 0);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == operations.len());
        assert(forall|k: int| 0 <= k < operations@.len() ==> sum(operations@.take(k).map(|_idx, j: i32| j as int)) >= 0);
        assert(sum(operations@.take(operations@.len()).map(|_idx, j: i32| j as int)) >= 0);
        assert(forall|k: int| 0 <= k <= operations@.len() ==> sum(operations@.take(k).map(|_idx, j: i32| j as int)) >= 0);
    }
    
    false
}
// </vc-code>

}
fn main() {}