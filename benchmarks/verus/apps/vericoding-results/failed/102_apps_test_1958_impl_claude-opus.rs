// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, p: int, buyers: Seq<&str>) -> bool {
    1 <= n <= 40 &&
    2 <= p <= 1000 &&
    p % 2 == 0 &&
    buyers.len() == n &&
    forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
}

spec fn compute_total_payment(buyers: Seq<&str>, p: int) -> int
    recommends p >= 0,
                p % 2 == 0,
                forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
{
    compute_payment_backward(buyers, p, buyers.len() - 1, 0)
}

spec fn compute_payment_backward(buyers: Seq<&str>, p: int, current_index: int, current_apples: int) -> int
    recommends p >= 0,
                p % 2 == 0,
                -1 <= current_index < buyers.len(),
                current_apples >= 0,
                forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    decreases current_index + 1
{
    if current_index < 0 {
        0
    } else {
        let new_apples = if buyers[current_index] == "halfplus" { 
                            current_apples * 2 + 1
                         } else { 
                            current_apples * 2
                         };
        let payment = if buyers[current_index] == "halfplus" { 
                          (new_apples / 2) * p
                       } else { 
                          current_apples * p
                       };
        payment + compute_payment_backward(buyers, p, current_index - 1, new_apples)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add decreases clauses and fix pow2 lemmas */
proof fn lemma_apples_bounded(buyers: Seq<&str>, n: int)
    requires
        1 <= n <= 40,
        buyers.len() == n,
        forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures
        forall|k: int| 0 <= k <= n ==> compute_apples_at(buyers, k) <= pow2(k) - 1
{
    assert forall|k: int| 0 <= k <= n implies compute_apples_at(buyers, k) <= pow2(k) - 1 by {
        lemma_apples_at_bounded(buyers, k);
    }
}

proof fn lemma_apples_at_bounded(buyers: Seq<&str>, k: int)
    requires
        0 <= k <= buyers.len(),
        forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures
        compute_apples_at(buyers, k) <= pow2(k) - 1
    decreases k
{
    if k == 0 {
        assert(compute_apples_at(buyers, 0) == 0);
        assert(pow2(0) == 1);
    } else {
        lemma_apples_at_bounded(buyers, k - 1);
        let prev = compute_apples_at(buyers, k - 1);
        assert(prev <= pow2(k - 1) - 1);
        let curr = compute_apples_at(buyers, k);
        if buyers[buyers.len() - k] == "halfplus" {
            assert(curr == prev * 2 + 1);
            assert(curr <= (pow2(k - 1) - 1) * 2 + 1);
            assert(curr <= pow2(k) - 2 + 1);
            assert(curr <= pow2(k) - 1);
        } else {
            assert(curr == prev * 2);
            assert(curr <= (pow2(k - 1) - 1) * 2);
            assert(curr <= pow2(k) - 2);
            assert(curr <= pow2(k) - 1);
        }
    }
}

proof fn lemma_pow2_properties()
    ensures
        pow2(0) == 1,
        pow2(1) == 2,
        pow2(2) == 4,
        pow2(3) == 8,
        pow2(4) == 16,
        pow2(5) == 32,
        pow2(6) == 64,
        pow2(7) == 128,
        forall|k: int| 0 <= k <= 7 ==> pow2(k) <= 128
{
    assert(pow2(0) == 1);
    assert(pow2(1) == 2);
    assert(pow2(2) == 4);
    assert(pow2(3) == 8);
    assert(pow2(4) == 16);
    assert(pow2(5) == 32);
    assert(pow2(6) == 64);
    assert(pow2(7) == 128);
}

spec fn pow2(n: int) -> int
    decreases n
{
    if n <= 0 { 1 } else { 2 * pow2(n - 1) }
}

spec fn compute_apples_at(buyers: Seq<&str>, k: int) -> int
    recommends
        0 <= k <= buyers.len(),
        forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    decreases k
{
    if k == 0 {
        0
    } else {
        let prev_apples = compute_apples_at(buyers, k - 1);
        if buyers[buyers.len() - k] == "halfplus" {
            prev_apples * 2 + 1
        } else {
            prev_apples * 2
        }
    }
}

spec fn compute_total_at(buyers: Seq<&str>, p: int, k: int) -> int
    recommends
        p >= 0,
        p % 2 == 0,
        0 <= k <= buyers.len(),
        forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    decreases k
{
    if k == 0 {
        0
    } else {
        let prev_apples = compute_apples_at(buyers, k - 1);
        let payment = if buyers[buyers.len() - k] == "halfplus" {
            ((prev_apples * 2 + 1) / 2) * p
        } else {
            prev_apples * p
        };
        compute_total_at(buyers, p, k - 1) + payment
    }
}

proof fn lemma_compute_equivalence(buyers: Seq<&str>, p: int, n: int)
    requires
        1 <= n <= 40,
        2 <= p <= 1000,
        p % 2 == 0,
        buyers.len() == n,
        forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures
        compute_total_at(buyers, p, n) == compute_total_payment(buyers, p)
{
    assert(compute_total_payment(buyers, p) == compute_payment_backward(buyers, p, n - 1, 0));
    lemma_backward_forward_equiv(buyers, p, n - 1, 0);
}

proof fn lemma_backward_forward_equiv(buyers: Seq<&str>, p: int, idx: int, apples: int)
    requires
        p >= 0,
        p % 2 == 0,
        -1 <= idx < buyers.len(),
        apples == compute_apples_at(buyers, buyers.len() as int - 1 - idx),
        forall|i: int| 0 <= i < buyers.len() ==> buyers[i] == "half" || buyers[i] == "halfplus"
    ensures
        compute_payment_backward(buyers, p, idx, apples) == compute_total_at(buyers, p, buyers.len() as int) - compute_total_at(buyers, p, buyers.len() as int - 1 - idx)
    decreases idx + 1
{
    if idx < 0 {
        assert(compute_payment_backward(buyers, p, idx, apples) == 0);
        assert(buyers.len() as int - 1 - idx == buyers.len() as int);
        assert(compute_total_at(buyers, p, buyers.len() as int) - compute_total_at(buyers, p, buyers.len() as int) == 0);
    } else {
        let k = buyers.len() as int - 1 - idx;
        assert(0 <= k < buyers.len());
        let new_apples = if buyers[idx] == "halfplus" { apples * 2 + 1 } else { apples * 2 };
        let payment = if buyers[idx] == "halfplus" { (new_apples / 2) * p } else { apples * p };
        assert(new_apples == compute_apples_at(buyers, k + 1));
        lemma_backward_forward_equiv(buyers, p, idx - 1, new_apples);
        assert(compute_payment_backward(buyers, p, idx - 1, new_apples) == compute_total_at(buyers, p, buyers.len() as int) - compute_total_at(buyers, p, k + 1));
        assert(compute_payment_backward(buyers, p, idx, apples) == payment + compute_payment_backward(buyers, p, idx - 1, new_apples));
        assert(compute_total_at(buyers, p, k + 1) - compute_total_at(buyers, p, k) == payment);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, buyers: Vec<&str>) -> (result: i8)
    requires valid_input(n as int, p as int, buyers@)
    ensures result >= 0,
            result as int == compute_total_payment(buyers@, p as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix pow2 proofs and bounds checking */
    let mut apples: i8 = 0;
    let mut total: i8 = 0;
    let mut i: usize = n as usize;
    
    proof {
        lemma_apples_bounded(buyers@, n as int);
        lemma_compute_equivalence(buyers@, p as int, n as int);
        lemma_pow2_properties();
    }
    
    while i > 0
        invariant
            0 <= i <= n,
            n == buyers.len(),
            valid_input(n as int, p as int, buyers@),
            apples >= 0,
            total >= 0,
            i <= buyers.len(),
            apples as int == compute_apples_at(buyers@, (n - i) as int),
            total as int == compute_total_at(buyers@, p as int, (n - i) as int),
            apples <= 127,
            total <= 127,
        decreases i
    {
        i = i - 1;
        
        proof {
            lemma_apples_bounded(buyers@, n as int);
            lemma_pow2_properties();
            assert(0 <= (n - i) as int <= n);
            assert((n - i) as int <= 40);
            assert(compute_apples_at(buyers@, (n - i) as int) <= pow2((n - i) as int) - 1);
            if (n - i) as int <= 7 {
                assert(pow2((n - i) as int) <= 128);
                assert(compute_apples_at(buyers@, (n - i) as int) <= 127);
            } else {
                assert((n - i) as int <= 40);
                assert(compute_apples_at(buyers@, (n - i) as int) <= pow2(7) - 1);
                assert(compute_apples_at(buyers@, (n - i) as int) <= 127);
            }
        }
        
        let is_halfplus = match buyers[i] {
            "halfplus" => true,
            _ => false,
        };
        
        if is_halfplus {
            proof {
                assert(buyers@[i as int] == "halfplus");
                lemma_apples_bounded(buyers@, n as int);
                lemma_pow2_properties();
                assert(0 <= (n - i) as int + 1 <= n);
                assert((n - i) as int + 1 <= 40);
                if (n - i) as int + 1 <= 7 {
                    assert(compute_apples_at(buyers@, (n - i) as int + 1) <= pow2((n - i) as int + 1) - 1);
                    assert(pow2((n - i) as int + 1) <= 128);
                    assert(compute_apples_at(buyers@, (n - i) as int + 1) <= 127);
                } else {
                    assert(compute_apples_at(buyers@, (n - i) as int + 1) <= pow2(7) - 1);
                    assert(compute_apples_at(buyers@, (n - i) as int + 1) <= 127);
                }
                assert(apples as int * 2 + 1 <= 127);
            }
            apples = apples * 2 + 1;
            let payment = (apples / 2) * p;
            proof {
                assert(payment <= 63 * p);
                assert(payment <= 63 * 1000);
                assert(payment <= 127);
                assert(total as int + payment as int <= 127);
            }
            total = total + payment;
        } else {
            proof {
                assert(buyers@[i as int] == "half");
                lemma_apples_bounded(buyers@, n as int);
                lemma_pow2_properties();
                assert(0 <= (n - i) as int + 1 <= n);
                assert((n - i) as int + 1 <= 40);
                if (n - i) as int + 1 <= 7 {
                    assert(compute_apples_at(buyers@, (n - i) as int + 1) <= pow2((n - i) as int + 1) - 1);
                    assert(pow2((n - i) as int + 1) <= 128);
                    assert(compute_apples_at(buyers@, (n - i) as int + 1) <= 127);
                } else {
                    assert(compute_apples_at(buyers@, (n - i) as int + 1) <= pow2(7) - 1);
                    assert(compute_apples_at(buyers@, (n - i) as int + 1) <= 127);
                }
                assert(apples as int * 2 <= 127);
            }
            let payment = apples * p;
            proof {
                assert(payment <= 127);
            }
            apples = apples * 2;
            proof {
                assert(total as int + payment as int <= 127);
            }
            total = total + payment;
        }
        
        proof {
            assert(apples as int == compute_apples_at(buyers@, (n - i) as int + 1));
            assert(total as int == compute_total_at(buyers@, p as int, (n - i) as int + 1));
        }
    }
    
    proof {
        assert(i == 0);
        assert((n - i) as int == n);
        assert(total as int == compute_total_at(buyers@, p as int, n as int));
        lemma_compute_equivalence(buyers@, p as int, n as int);
        assert(total as int == compute_total_payment(buyers@, p as int));
    }
    
    total
}
// </vc-code>


}

fn main() {}