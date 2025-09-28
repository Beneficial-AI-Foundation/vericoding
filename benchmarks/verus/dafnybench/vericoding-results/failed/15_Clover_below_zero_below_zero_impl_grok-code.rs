use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < (result.0.len() - 1) as int ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == true ==> exists|i: int| 1 <= i <= operations.len() as int && result.0[i] < 0,
        result.1 == false ==> forall|i: int| 0 <= i < result.0.len() as int ==> result.0[i] >= 0,
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    let mut balance = 0;
    let mut balances = Vec::new();
    balances.push(balance);
    let mut went_negative = false;
    let ops_len = operations.len();
    while i < ops_len
        invariant
            balances@.len() == i as int + 1,
            balances@[0] == 0,
            forall|j: int| 0 < j < balances@.len() ==> #[trigger] balances@[j] == balances@[j - 1] + operations@[j - 1],
            (went_negative == true) <==> exists|k: int| 1 <= k < balances@.len() && #[trigger] balances@[k] < 0,
            (went_negative == false) ==> forall|k: int| 0 <= k < balances@.len() ==> #[trigger] balances@[k] >= 0,
        decreases ops_len - i
    {
        balance = balance + operations[i];
        balances.push(balance);
        proof {
            assert(balances@[i as int + 1] == balances@[i as int] + operations@[i as int]);
            if went_negative == false && balance < 0 {
                assert(went_negative == true);
            }
        }
        if balance < 0 {
            went_negative = true;
        }
        i += 1;
    }
    (balances, went_negative)
}
// </vc-code>

fn main() {}

}