use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse_div,
};
use vstd::prelude::*;

verus! {

spec fn mul(a: nat, b: nat) -> (result:nat) {
    builtin::mul(a, b)
}
// pure-end

spec fn divides(factor: nat, candidate: nat) -> (result:bool) {
    exists|k: nat| mul(factor, k) == candidate
}
// pure-end

proof fn lemma_mod_zero(a: nat, b: nat)
    // pre-conditions-start
    requires
        a > 0 && b > 0,
        a % b == 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        divides(b, a),
    // post-conditions-end
{
    // impl-start
    lemma_fundamental_div_mod(a as int, b as int);
    assert(mul(b, (a / b)) == a);
    // impl-end
}
// pure-end

proof fn lemma_mod_zero_reversed(a: nat, b: nat)
    // pre-conditions-start
    requires
        a > 0 && b > 0,
        divides(b, a),
    // pre-conditions-end
    // post-conditions-start
    ensures
        a % b == 0,
    // post-conditions-end
{
    // impl-start
    let k_wit = choose|k: nat| mul(b, k) == a;
    assert(k_wit == a / b) by {
        lemma_fundamental_div_mod_converse_div(a as int, b as int, k_wit as int, 0 as int);
    }
    lemma_fundamental_div_mod(a as int, b as int);
    // impl-end
}
// pure-end

proof fn lemma_one_divides_all()
    // post-conditions-start
    ensures
        forall|v: nat| divides(1 as nat, v),
    // post-conditions-end
{
    // impl-start
    assert forall|v: nat| divides(1 as nat, v) by {
        assert(mul(1 as nat, v) == v);
    }
    // impl-end
}
// pure-end

fn largest_divisor(n: u32) -> (ret: u32)
    // pre-conditions-start
    requires
        n > 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        divides(ret as nat, n as nat),
        ret < n,
        forall|k: u32| (0 < k < n && divides(k as nat, n as nat)) ==> ret >= k,
    // post-conditions-end
{
    let mut i = 2u32;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i * i <= n
        invariant
            2 <= i <= n,
            forall|j: u32| (2 <= j < i) ==> n % j != 0,
        decreases n - i
    {
        if n % i == 0 {
            /* code modified by LLM (iteration 1): wrapped lemma call in proof block to allow nat types */
            proof {
                lemma_mod_zero(n as nat, i as nat);
            }
            let result = n / i;
            assert(mul(i as nat, result as nat) == n as nat);
            assert(result < n) by {
                assert(i >= 2);
                assert(mul(i as nat, result as nat) == n as nat);
                assert(result <= n / 2);
            }
            
            assert(forall|k: u32| (0 < k < n && divides(k as nat, n as nat)) ==> result >= k) by {
                assert forall|k: u32| (0 < k < n && divides(k as nat, n as nat)) implies result >= k by {
                    if k > result {
                        let k_witness = choose|m: nat| mul(k as nat, m) == n as nat;
                        assert(k_witness < i) by {
                            if k_witness >= i {
                                /* code modified by LLM (iteration 1): fixed type casting for mul function calls */
                                assert(mul(k as nat, k_witness) >= mul((result + 1) as nat, i as nat));
                                assert(mul((result + 1) as nat, i as nat) > mul(result as nat, i as nat));
                                assert(mul(result as nat, i as nat) == n as nat);
                                assert(false);
                            }
                        }
                        if k_witness >= 2 {
                            /* code modified by LLM (iteration 1): fixed type casting for modulo operation */
                            assert((n as nat) % k_witness == 0) by {
                                lemma_mod_zero_reversed(n as nat, k_witness);
                            }
                            assert(false);
                        } else {
                            assert(k_witness == 1);
                            assert(k == n);
                            assert(false);
                        }
                    }
                }
            }
            return result;
        }
        i = i + 1;
    }
    
    // n is prime, so its largest proper divisor is 1
    /* code modified by LLM (iteration 1): wrapped lemma call in proof block to fix compilation error */
    proof {
        lemma_one_divides_all();
    }
    assert(divides(1, n as nat));
    
    assert(forall|k: u32| (0 < k < n && divides(k as nat, n as nat)) ==> 1 >= k) by {
        assert forall|k: u32| (0 < k < n && divides(k as nat, n as nat)) implies 1 >= k by {
            if k > 1 {
                assert(k >= 2);
                if k * k <= n {
                    assert(n % k == 0) by {
                        lemma_mod_zero_reversed(n as nat, k as nat);
                    }
                    assert(false);
                } else {
                    let k_witness = choose|m: nat| mul(k as nat, m) == n as nat;
                    assert(k_witness < k) by {
                        if k_witness >= k {
                            assert(mul(k as nat, k_witness) >= mul(k as nat, k as nat));
                            assert(mul(k as nat, k as nat) > n as nat);
                            assert(false);
                        }
                    }
                    assert(k_witness >= 2) by {
                        if k_witness == 1 {
                            assert(k == n);
                            assert(false);
                        }
                    }
                    assert(k_witness * k_witness <= n) by {
                        assert(k_witness < k);
                        assert(mul(k as nat, k_witness) == n as nat);
                        assert(k_witness * k < n + k_witness);
                        assert(k_witness * k_witness < k_witness * k);
                        assert(k_witness * k_witness <= n);
                    }
                    /* code modified by LLM (iteration 1): fixed type casting for modulo operation */
                    assert((n as nat) % (k_witness as nat) == 0) by {
                        lemma_mod_zero_reversed(n as nat, k_witness as nat);
                    }
                    assert(false);
                }
            }
        }
    }
    
    1
}

}
fn main() {}