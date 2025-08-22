use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse_div,
};
use vstd::prelude::*;

verus! {

spec fn mul(a: nat, b: nat) -> (result:nat) {
    /* code modified by LLM (iteration 1): replaced builtin::mul with standard multiplication */
    a * b
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
    let mut i = n - 1;
    while i > 0
        invariant
            0 < i < n,
            forall|k: u32| (i < k < n) ==> !divides(k as nat, n as nat),
        /* code modified by LLM (iteration 2): added decreases clause for loop termination */
        decreases i
    {
        if n % i == 0 {
            proof {
                lemma_mod_zero(n as nat, i as nat);
            }
            assert(divides(i as nat, n as nat));
            assert(forall|k: u32| (0 < k < n && divides(k as nat, n as nat)) ==> i >= k) by {
                assert(forall|k: u32| (i < k < n) ==> !divides(k as nat, n as nat));
            };
            return i;
        }
        i -= 1;
    }
    
    proof {
        lemma_one_divides_all();
        assert(divides(1 as nat, n as nat));
        assert(forall|k: u32| (0 < k < n && divides(k as nat, n as nat)) ==> 1 >= k) by {
            assert(forall|k: u32| (1 < k < n) ==> !divides(k as nat, n as nat));
        };
    }
    1
}

}
fn main() {}