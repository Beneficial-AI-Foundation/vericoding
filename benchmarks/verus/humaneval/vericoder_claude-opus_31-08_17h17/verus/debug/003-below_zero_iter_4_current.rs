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

// <vc-helpers>
proof fn sum_empty()
    ensures sum(Seq::<int>::empty()) == 0,
{
}

proof fn sum_single(x: int)
    ensures sum(seq![x]) == x,
{
    assert(seq![x].len() == 1);
    assert(seq![x][0] == x);
    assert(seq![x].skip(1) =~= Seq::<int>::empty());
    assert(sum(seq![x].skip(1)) == 0);
}

proof fn sum_append_one(s: Seq<int>, x: int)
    ensures sum(s.push(x)) == sum(s) + x,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s =~= Seq::<int>::empty());
        assert(s.push(x) =~= seq![x]);
        sum_single(x);
        assert(sum(s) == 0);
        assert(sum(s.push(x)) == x);
    } else {
        assert(s.push(x)[0] == s[0]);
        assert(s.push(x).skip(1) =~= s.skip(1).push(x));
        sum_append_one(s.skip(1), x);
        assert(sum(s.push(x).skip(1)) == sum(s.skip(1).push(x)));
        assert(sum(s.skip(1).push(x)) == sum(s.skip(1)) + x);
        assert(sum(s.push(x)) == s.push(x)[0] + sum(s.push(x).skip(1)));
        assert(sum(s.push(x)) == s[0] + sum(s.skip(1)) + x);
        assert(sum(s) == s[0] + sum(s.skip(1)));
    }
}

proof fn sum_take_plus_one(s: Seq<int>, i: int)
    requires 0 <= i < s.len(),
    ensures sum(s.take(i + 1)) == sum(s.take(i)) + s[i],
{
    assert(s.take(i + 1) =~= s.take(i).push(s[i]));
    sum_append_one(s.take(i), s[i]);
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    let mut balance: i32 = 0;
    let mut i: usize = 0;
    
    while i < operations.len()
        invariant
            0 <= i <= operations.len(),
            balance as int == sum(operations@.take(i as int).map(|_idx, j: i32| j as int)),
            forall|j: int| 0 <= j <= i ==> sum(operations@.take(j).map(|_idx, k: i32| k as int)) >= 0,
            sum(operations@.take((i + 1) as int).map(|_idx, j: i32| j as int)) <= i32::MAX,
        decreases operations.len() - i,
    {
        let old_balance = balance;
        let old_i = i;
        
        proof {
            assert(sum(operations@.take((old_i + 1) as int).map(|_idx, j: i32| j as int)) <= i32::MAX);
            let ops_seq = operations@.map(|_idx, j: i32| j as int);
            assert(operations@.take((old_i + 1) as int).map(|_idx, j: i32| j as int) 
                   =~= ops_seq.take((old_i + 1) as int));
            sum_take_plus_one(ops_seq, old_i as int);
            assert(sum(ops_seq.take((old_i + 1) as int)) == sum(ops_seq.take(old_i as int)) + ops_seq[old_i as int]);
            assert(sum(operations@.take((old_i + 1) as int).map(|_idx, j: i32| j as int))
                   == sum(operations@.take(old_i as int).map(|_idx, j: i32| j as int)) + operations@[old_i as int] as int);
            assert(old_balance as int == sum(operations@.take(old_i as int).map(|_idx, j: i32| j as int)));
            assert(sum(operations@.take((old_i + 1) as int).map(|_idx, j: i32| j as int)) 
                   == old_balance as int + operations@[old_i as int] as int);
            assert(old_balance as int + operations@[old_i as int] as int <= i32::MAX);
            assert(old_balance as int + operations@[old_i as int] as int >= i32::MIN);
        }
        
        balance = balance + operations[i];
        i = i + 1;
        
        proof {
            assert(balance as int == old_balance as int + operations@[old_i as int] as int);
            assert(i == old_i + 1);
            assert(balance as int == sum(operations@.take(i as int).map(|_idx, j: i32| j as int)));
        }
        
        if balance < 0 {
            assert(sum(operations@.take(i as int).map(|_idx, j: i32| j as int)) < 0);
            return true;
        }
    }
    
    assert(forall|j: int| 0 <= j <= operations@.len() ==> 
           sum(operations@.take(j).map(|_idx, k: i32| k as int)) >= 0);
    false
}
// </vc-code>

fn main() {}
}