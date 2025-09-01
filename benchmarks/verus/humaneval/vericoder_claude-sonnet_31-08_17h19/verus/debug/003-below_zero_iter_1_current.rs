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
proof fn sum_prefix_lemma(operations: Seq<int>, i: nat)
    requires i <= operations.len()
    ensures sum(operations.take(i as int)) == {
        let mut total = 0int;
        let mut j = 0;
        while j < i {
            total = total + operations[j as int];
            j = j + 1;
        }
        total
    }
    decreases i
{
    if i == 0 {
        assert(operations.take(0).len() == 0);
    } else {
        sum_prefix_lemma(operations, (i - 1) as nat);
        assert(operations.take(i as int) == operations.take((i - 1) as int).push(operations[(i - 1) as int]));
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
        
        assert(operations@.take(i as int) == operations@.take((i - 1) as int).push(operations[(i - 1) as int]));
        assert(operations@.take(i as int).map(|_idx, j: i32| j as int) == 
               operations@.take((i - 1) as int).map(|_idx, j: i32| j as int).push(operations[(i - 1) as int] as int));
    }
    
    false
}
// </vc-code>

fn main() {}
}