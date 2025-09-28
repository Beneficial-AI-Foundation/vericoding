// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn compute_sequence(operations: Seq<int>) -> (res: Seq<int>, has_negative: bool) 
    ensures
        res.len() == operations.len() + 1,
        res[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> res[i + 1] == res[i] + operations[i],
        has_negative == (exists|i: int| 1 <= i < res.len() && res[i] < 0)
{
    /* helper modified by LLM (iteration 5): Fixed function signature syntax */
    let mut res = Seq::empty();
    res = res.push(0);
    let mut j: int = 0;
    let mut has_negative = false;
    
    while j < operations.len()
        invariant
            res.len() == j + 1,
            res[0] == 0,
            forall|k: int| 0 <= k < j ==> res[k + 1] == res[k] + operations[k],
            has_negative == (exists|k: int| 1 <= k < res.len() && res[k] < 0),
        decreases operations.len() - j
    {
        let next_val = res[j] + operations[j];
        res = res.push(next_val);
        if next_val < 0 {
            has_negative = true;
        }
        j = j + 1;
    }
    (res, has_negative)
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: &Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == (exists|i: int| 1 <= i < result.0.len() && result.0[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed function signature syntax */
    let mut balance: i32 = 0;
    let mut balances = Vec::new();
    let mut found_negative = false;
    
    balances.push(0);
    
    let ghost operations_seq = operations@;
    let mut i: usize = 0;
    
    while i < operations.len()
        invariant
            balances@.len() == i + 1,
            balance == operations_seq.subrange(0, i as int).sum(),
            forall|j: int| 0 <= j < i as int ==> balances@[j + 1] == balances@[j] + operations_seq[j],
            found_negative == (exists|j: int| 1 <= j < balances@.len() && balances@[j] < 0)
    {
        balance = balance + operations[i];
        balances.push(balance);
        if balance < 0 {
            found_negative = true;
        }
        i = i + 1;
    }
    
    (balances, found_negative)
}
// </vc-code>

}
fn main() {}