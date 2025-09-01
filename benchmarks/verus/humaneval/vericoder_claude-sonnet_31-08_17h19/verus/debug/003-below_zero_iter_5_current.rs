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
proof fn sum_push_lemma(s: Seq<int>, x: int)
    ensures sum(s.push(x)) == sum(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        assert(s =~= Seq::<int>::empty());
        assert(s.push(x) =~= seq![x]);
        assert(sum(s.push(x)) == x);
        assert(sum(s) == 0);
    } else {
        assert(s.push(x) == seq![s[0]].add(s.skip(1).push(x)));
        sum_push_lemma(s.skip(1), x);
        assert(sum(s.skip(1).push(x)) == sum(s.skip(1)) + x);
        assert(sum(s.push(x)) == s[0] + sum(s.skip(1).push(x)));
        assert(sum(s.push(x)) == s[0] + sum(s.skip(1)) + x);
        assert(sum(s) == s[0] + sum(s.skip(1)));
    }
}

proof fn sum_take_lemma(s: Seq<int>, i: nat, j: nat)
    requires i <= j <= s.len()
    ensures sum(s.take(i as int)) + sum(s.subrange(i as int, j as int)) == sum(s.take(j as int))
    decreases j - i
{
    if i == j {
        assert(s.subrange(i as int, j as int) =~= Seq::<int>::empty());
        assert(sum(s.subrange(i as int, j as int)) == 0);
        assert(s.take(i as int) =~= s.take(j as int));
    } else {
        let mid = j - 1;
        sum_take_lemma(s, i, mid);
        assert(s.take(j as int) == s.take(mid as int).push(s[mid as int]));
        sum_push_lemma(s.take(mid as int), s[mid as int]);
        assert(sum(s.take(j as int)) == sum(s.take(mid as int)) + s[mid as int]);
    }
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
    
    while i <= operations.len()
        invariant
            i <= operations.len(),
            balance == sum(operations@.take(i as int).map(|_idx, j: i32| j as int)),
            forall|k: int| 0 <= k < i ==> sum(operations@.take(k).map(|_idx, j: i32| j as int)) >= 0,
    {
        if balance < 0 {
            return true;
        }
        
        if i == operations.len() {
            break;
        }
        
        balance = balance + operations[i];
        i = i + 1;
        
        proof {
            let ops_as_int = operations@.map(|_idx, j: i32| j as int);
            let prev_seq = ops_as_int.take((i - 1) as int);
            let curr_seq = ops_as_int.take(i as int);
            let new_elem = operations[(i - 1) as int] as int;
            
            assert(operations@.take(i as int) == operations@.take((i - 1) as int).push(operations[(i - 1) as int]));
            assert(curr_seq == prev_seq.push(new_elem));
            sum_push_lemma(prev_seq, new_elem);
            assert(sum(curr_seq) == sum(prev_seq) + new_elem);
        }
    }
    
    false
}
// </vc-code>

fn main() {}
}