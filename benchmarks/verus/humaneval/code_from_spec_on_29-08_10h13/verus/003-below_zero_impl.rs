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
proof fn sum_zero()
    ensures sum(Seq::<int>::empty()) == 0
{
}

proof fn sum_one_elem(x: int)
    ensures sum(seq![x]) == x
{
}

proof fn sum_prepend(x: int, s: Seq<int>)
    ensures sum(seq![x].add(s)) == x + sum(s)
{
}

proof fn sum_take_monotonic(s: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= s.len(),
    requires forall|k: int| 0 <= k < s.len() ==> s[k] >= 0,
    ensures sum(s.take(i)) <= sum(s.take(j))
    decreases j - i
{
    if i == j {
    } else {
        sum_take_monotonic(s, i + 1, j);
    }
}

proof fn sum_take_extends(s: Seq<int>, i: int)
    requires 0 <= i < s.len()
    ensures sum(s.take(i + 1)) == sum(s.take(i)) + s[i]
{
    let prefix = s.take(i + 1);
    let smaller_prefix = s.take(i);
    
    assert(prefix.len() == i + 1);
    assert(smaller_prefix.len() == i);
    assert(prefix == smaller_prefix.push(s[i]));
    
    if i == 0 {
        assert(smaller_prefix.len() == 0);
        assert(sum(smaller_prefix) == 0);
        assert(prefix == seq![s[0]]);
    } else {
        assert(prefix[0] == s[0]);
        assert(prefix.skip(1) == s.take(i));
        assert(sum(prefix) == prefix[0] + sum(prefix.skip(1)));
        assert(sum(prefix) == s[0] + sum(s.take(i)));
    }
}

proof fn map_take_extends(s: Seq<i32>, i: int)
    requires 0 <= i < s.len()
    ensures s.map(|_idx, j: i32| j as int).take(i + 1) == 
            s.take(i + 1).map(|_idx, j: i32| j as int)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def below_zero(operations: List[int]) -> bool"
docstring: |
You're given a list of deposit and withdrawal operations on a bank account that starts with
zero balance. Your task is to detect if at any point the balance of account fallls below zero, and
at that point function should return True. Otherwise it should return False.
test_cases:
- input:
- 1
- 2
- 3
expected_output: false
- input:
- 1
- 2
- -4
- 5
expected_output: true
*/
// </vc-description>

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
    /* code modified by LLM (iteration 5): fix balance tracking and return logic */
    let mut balance: i32 = 0;
    let mut i: usize = 0;
    
    if balance < 0 {
        proof {
            assert(sum(operations@.take(0).map(|_idx, j: i32| j as int)) == 0);
        }
    }
    
    while i < operations.len()
        invariant
            i <= operations.len(),
            balance == sum(operations@.take(i as int).map(|_idx, j: i32| j as int)),
            forall|k: int| 0 <= k <= i ==> sum(operations@.take(k).map(|_idx, j: i32| j as int)) <= i32::MAX,
            balance >= 0,
    {
        balance = balance + operations[i];
        
        proof {
            map_take_extends(operations@, i as int);
            sum_take_extends(operations@.map(|_idx, j: i32| j as int), i as int);
        }
        
        i = i + 1;
        
        if balance < 0 {
            proof {
                assert(exists|k: int| 0 <= k <= operations@.len() && 
                       sum(operations@.take(k).map(|_idx, j: i32| j as int)) < 0) by {
                    assert(sum(operations@.take(i as int).map(|_idx, j: i32| j as int)) < 0);
                }
            }
            return true;
        }
    }
    
    proof {
        assert(!(exists|k: int| 0 <= k <= operations@.len() && 
                 sum(operations@.take(k).map(|_idx, j: i32| j as int)) < 0)) by {
            assert(forall|k: int| 0 <= k <= operations@.len() ==> 
                   sum(operations@.take(k).map(|_idx, j: i32| j as int)) >= 0) by {
                assert(forall|k: int| 0 <= k <= i ==> 
                       sum(operations@.take(k).map(|_idx, j: i32| j as int)) >= 0);
                assert(i == operations@.len());
            }
        }
    }
    
    false
}
// </vc-code>

}
fn main() {}