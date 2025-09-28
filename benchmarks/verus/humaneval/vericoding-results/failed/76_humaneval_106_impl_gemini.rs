// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { n * factorial((n - 1) as nat) }
}

spec fn sum_range(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + sum_range((n - 1) as nat) }
}

spec fn valid_result(n: nat, result: Seq<nat>) -> bool
{
    result.len() == n &&
    forall|i: int| 0 <= i < n ==> 
        (if (i + 1) % 2 == 0 { result[i] == factorial((i + 1) as nat) }
         else { result[i] == sum_range((i + 1) as nat) })
}
// </vc-preamble>

// <vc-helpers>
fn compute_factorial(n: u8) -> (res: u8)
    requires
        n > 0,
        n <= 5,
    ensures
        res as nat == factorial(n as nat),
    decreases n
{
    lemma_factorial_values(n as nat);
    if n == 1 {
        1
    } else {
        let rec = compute_factorial(n - 1);
        (n as u8) * rec
    }
}

fn compute_sum_range(n: u8) -> (res: u8)
    requires
        n > 0,
        n <= 5,
    ensures
        res as nat == sum_range(n as nat),
    decreases n
{
    lemma_sum_range_values(n as nat);
    if n == 1 {
        1
    } else {
        let rec = compute_sum_range(n - 1);
        (n as u8) + rec
    }
}

lemma fn lemma_factorial_values(k: nat)
    requires k <= 5
    ensures
        k == 0 ==> factorial(k) == 1,
        k == 1 ==> factorial(k) == 1,
        k == 2 ==> factorial(k) == 2,
        k == 3 ==> factorial(k) == 6,
        k == 4 ==> factorial(k) == 24,
        k == 5 ==> factorial(k) == 120,
    decreases k
{
    if k > 0 {
        lemma_factorial_values((k - 1) as nat);
    }
}

lemma fn lemma_sum_range_values(k: nat)
    requires k <= 5
    ensures
        k == 0 ==> sum_range(k) == 0,
        k == 1 ==> sum_range(k) == 1,
        k == 2 ==> sum_range(k) == 3,
        k == 3 ==> sum_range(k) == 6,
        k == 4 ==> sum_range(k) == 10,
        k == 5 ==> sum_range(k) == 15,
    decreases k
{
    if k > 0 {
        lemma_sum_range_values((k - 1) as nat);
    }
}

lemma fn valid_result_append(n: nat, s: Seq<nat>, x: nat)
    requires
        valid_result(n, s),
        n < 255,
        (if (n + 1) % 2 == 0 { x == factorial((n + 1) as nat) } 
         else { x == sum_range((n + 1) as nat) }),
    ensures
        valid_result(n + 1, s.push(x)),
{
    let new_seq = s.push(x);
    assert(new_seq.len() == n + 1);
    assert forall|i: int| 0 <= i < n + 1 implies
        (if (i + 1) % 2 == 0 { new_seq[i] == factorial((i + 1) as nat) }
         else { new_seq[i] == sum_range((i + 1) as nat) })
    by {
        if i < n {
            assert(valid_result(n, s));
        } else { // i == n
            // this is proved by the requires clause on x
        }
    }
    assert(valid_result(n + 1, new_seq));
}
// </vc-helpers>

// <vc-spec>
fn f(n: u8) -> (result: Vec<u8>)
    ensures valid_result(n as nat, result@.map(|i: int, x: u8| x as nat))
// </vc-spec>
// <vc-code>
{
    if n > 5 {
        while true 
            invariant false
        {
        }
    }

    let mut result: Vec<u8> = Vec::new();
    let mut i: u8 = 0;
    while i < n
        invariant
            0 <= i <= n,
            i <= 5,
            result.len() == i as int,
            valid_result(i as nat, result@.map(|_j: int, x: u8| x as nat)),
        decreases n - i
    {
        let k = i + 1;
        let val = if k % 2 == 0 {
            compute_factorial(k)
        } else {
            compute_sum_range(k)
        };
        result.push(val);

        proof {
            let prev_seq = result@.subrange(0, i as int);
            let prev_seq_nat = prev_seq.map(|_j: int, x: u8| x as nat);
            
            valid_result_append(i as nat, prev_seq_nat, val as nat);

            let new_seq_nat = result@.map(|_j: int, x: u8| x as nat);
            assert(valid_result((i + 1) as nat, new_seq_nat));
        }
        
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}