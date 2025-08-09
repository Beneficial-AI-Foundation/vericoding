use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::assert_by_contradiction;
use vstd::calc;
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> (result:bool) {
    forall|i: nat| 1 < i < n ==> #[trigger] (n % i) != 0
}
// pure-end


spec fn is_prime_factorization(n: nat, factorization: Seq<nat>) -> (result:bool) {

    &&& forall|i: int|
        0 <= i < factorization.len() ==> #[trigger] is_prime(
            factorization[i] as nat,
        )
        
    &&& factorization.fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat)
        == n
        
    &&& forall|i: nat, j: nat|
        (1 < i <= j < factorization.len()) ==> (#[trigger] factorization[i as int]
            <= #[trigger] factorization[j as int])
}
// pure-end


proof fn lemma_fold_right_pull_out_nat(seq: Seq<nat>, k: nat)
    // post-conditions-start
    ensures
        seq.fold_right(|x, acc: nat| (acc * x) as nat, k) == (seq.fold_right(
            |x, acc: nat| (acc * x) as nat,
            1,
        ) * k) as nat,
    decreases seq.len(),
    // post-conditions-end
{
    if seq.len() == 0 {
        assert(seq.fold_right(|x, acc: nat| (acc * x) as nat, k) == k);
        assert(seq.fold_right(|x, acc: nat| (acc * x) as nat, 1) == 1);
    } else {
        let tail = seq.drop_last();
        let last = seq.last();
        lemma_fold_right_pull_out_nat(tail, k);
        assert(seq.fold_right(|x, acc: nat| (acc * x) as nat, k) == 
               (tail.fold_right(|x, acc: nat| (acc * x) as nat, k) * last) as nat);
        assert(seq.fold_right(|x, acc: nat| (acc * x) as nat, 1) == 
               (tail.fold_right(|x, acc: nat| (acc * x) as nat, 1) * last) as nat);
    }
}
// pure-end

proof fn lemma_fold_right_pull_out_hybrid(seq: Seq<u8>, k: nat)
    // post-conditions-start
    ensures
        seq.fold_right(|x, acc: nat| (acc * x) as nat, k) == (seq.fold_right(
            |x, acc: nat| (acc * x) as nat,
            1,
        ) * k) as nat,
    decreases seq.len(),
    // post-conditions-end
{
    if seq.len() == 0 {
        assert(seq.fold_right(|x, acc: nat| (acc * x) as nat, k) == k);
        assert(seq.fold_right(|x, acc: nat| (acc * x) as nat, 1) == 1);
    } else {
        let tail = seq.drop_last();
        let last = seq.last();
        lemma_fold_right_pull_out_hybrid(tail, k);
        assert(seq.fold_right(|x, acc: nat| (acc * x) as nat, k) == 
               (tail.fold_right(|x, acc: nat| (acc * x) as nat, k) * last as nat) as nat);
        assert(seq.fold_right(|x, acc: nat| (acc * x) as nat, 1) == 
               (tail.fold_right(|x, acc: nat| (acc * x) as nat, 1) * last as nat) as nat);
    }
}
// pure-end

proof fn lemma_unfold_right_fold(factors: Seq<u8>, old_factors: Seq<u8>, k: u8, m: u8)
    // pre-conditions-start
    requires
        old_factors.push(m) == factors,
        k % m == 0,
        m != 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        factors.fold_right(|x, acc: nat| (acc * x) as nat, ((k / m) as nat))
            == old_factors.fold_right(|x, acc: nat| (acc * x) as nat, ((k as nat))),
    // post-conditions-end
{
    assert(factors.fold_right(|x, acc: nat| (acc * x) as nat, ((k / m) as nat))
           == (old_factors.fold_right(|x, acc: nat| (acc * x) as nat, ((k / m) as nat)) * m as nat));
    lemma_fold_right_pull_out_hybrid(old_factors, (k / m) as nat);
    assert(old_factors.fold_right(|x, acc: nat| (acc * x) as nat, ((k / m) as nat))
           == (old_factors.fold_right(|x, acc: nat| (acc * x) as nat, 1) * (k / m) as nat));
    lemma_fundamental_div_mod(k as int, m as int);
    assert((k / m) as nat * m as nat == k as nat);
}
// pure-end

proof fn lemma_unfold_right_fold_new(factors: Seq<u8>, old_factors: Seq<u8>, m: u8)
    // pre-conditions-start
    requires
        old_factors.push(m as u8) == factors,
        m != 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        factors.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == old_factors.fold_right(
            |x, acc: nat| (acc * x) as nat,
            1nat,
        ) * (m as nat),
    // post-conditions-end
{
    assert(factors.fold_right(|x, acc: nat| (acc * x) as nat, 1nat)
           == (old_factors.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) * m as nat));
}
// pure-end

proof fn lemma_multiple_mod_is_zero(m: int, n: int, k: int)
    // pre-conditions-start
    requires
        n % k == 0,
        k % m == 0,
        k > 0,
        m > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        n % (k / m) == 0,
    // post-conditions-end
{
    lemma_mod_auto();
    assert(n == (n / k) * k);
    assert(k == (k / m) * m);
    assert(n == (n / k) * (k / m) * m);
    assert(n == ((n / k) * m) * (k / m));
}
// pure-end

proof fn lemma_multiple_mod_is_zero_new(m: int, n: int, k: int)
    // pre-conditions-start
    requires
        n % k == 0,
        k % m == 0,
        k > 0,
        m > 0,
        n > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        m * (n / k) == n / (k / m),
    // post-conditions-end
{
    lemma_mod_auto();
    assert(n == (n / k) * k);
    assert(k == (k / m) * m);
    assert(n == (n / k) * (k / m) * m);
    assert(n / (k / m) == (n / k) * m);
}
// pure-end

proof fn lemma_factor_mod_is_zero(k: int, m: int, j: int)
    // pre-conditions-start
    requires
        k % j != 0,
        k % m == 0,
        1 <= j < m,
    // pre-conditions-end
    // post-conditions-start
    ensures
        (k / m) % j != 0,
    // post-conditions-end
{
    if (k / m) % j == 0 {
        lemma_mod_auto();
        assert(k / m == ((k / m) / j) * j);
        assert(k == m * (k / m));
        assert(k == m * ((k / m) / j) * j);
        assert(k % j == 0);
        assert(false);
    }
}
// pure-end

proof fn lemma_mod_zero_twice(k: int, m: int, i: int)
    // pre-conditions-start
    requires
        k % m == 0,
        m % i == 0,
        m > 0,
        i > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        k % i == 0,
    // post-conditions-end
{
    lemma_mod_auto();
    assert(k == (k / m) * m);
    assert(m == (m / i) * i);
    assert(k == (k / m) * (m / i) * i);
}
// pure-end

proof fn lemma_first_divisor_is_prime(k: nat, m: nat)
    // pre-conditions-start
    requires
        k % m == 0,
        forall|j: nat| 1 < j < m ==> #[trigger] (k % j) != 0,
        m >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_prime(m),
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): fixed syntax error - removed block syntax and made it a proper forall expression */
    assert(forall|i: nat| 1 < i < m ==> #[trigger] (m % i) != 0) by {
        if exists|i: nat| 1 < i < m && m % i == 0 {
            let i = choose|i: nat| 1 < i < m && m % i == 0;
            lemma_mod_zero_twice(k as int, m as int, i as int);
            assert(k % i == 0);
            assert(false);
        }
    };
}
// pure-end

proof fn lemma_drop_last_map_commute(seq: Seq<u8>)
    // pre-conditions-start
    requires
        seq.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        seq.map(|_idx, j: u8| j as nat).drop_last() == seq.drop_last().map(|_idx, j: u8| j as nat),
    // post-conditions-end
{
    let mapped_then_dropped = seq.map(|_idx, j: u8| j as nat).drop_last();
    let dropped_then_mapped = seq.drop_last().map(|_idx, j: u8| j as nat);
    
    assert(mapped_then_dropped.len() == dropped_then_mapped.len());
    
    forall|i: int| 0 <= i < mapped_then_dropped.len() ensures mapped_then_dropped[i] == dropped_then_mapped[i] {
        assert(mapped_then_dropped[i] == seq[i] as nat);
        assert(dropped_then_mapped[i] == seq.drop_last()[i] as nat);
        assert(seq.drop_last()[i] == seq[i]);
    }
}
// pure-end

proof fn lemma_fold_right_equivalent_for_nat_u8(factorization: Seq<u8>)
    // pre-conditions-start
    requires
        factorization.fold_right(|x, acc: u8| (acc * x) as u8, 1u8) <= u8::MAX as u8,
        forall|i: int| 0 <= i < factorization.len() ==> factorization[i] > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        factorization.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == factorization.map(
            |_idx, j: u8| j as nat,
        ).fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat),
    decreases factorization.len(),
    // post-conditions-end
{
    if factorization.len() == 0 {
        assert(factorization.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == 1);
        assert(factorization.map(|_idx, j: u8| j as nat).fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat) == 1);
    } else {
        let tail = factorization.drop_last();
        let last = factorization.last();
        lemma_fold_right_equivalent_for_nat_u8(tail);
        assert(factorization.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == 
               (tail.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) * last as nat));
        assert(factorization.map(|_idx, j: u8| j as nat).fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat) == 
               (tail.map(|_idx, j: u8| j as nat).fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat) * last as nat));
    }
}
// pure-end

fn factorize(n: u8) -> (factorization: Vec<u8>)
    // pre-conditions-start
    requires
        1 <= n <= u8::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_prime_factorization(n as nat, factorization@.map(|_idx, j: u8| j as nat)),
    // post-conditions-end
{
    let mut factors: Vec<u8> = Vec::new();
    let mut k = n;
    let mut m = 2u8;
    
    while k > 1
        invariant
            1 <= k <= n,
            2 <= m <= n + 1,
            factors@.fold_right(|x, acc: nat| (acc * x) as nat, k as nat) == n as nat,
            forall|j: nat| 1 < j < m ==> (k as nat) % j != 0,
            forall|i: int| 0 <= i < factors@.len() ==> is_prime(factors@[i] as nat),
            forall|i: int| 0 <= i < factors@.len() ==> factors@[i] >= 2,
            forall|i: nat, j: nat| 
                (0 <= i <= j < factors@.len()) ==> 
                (#[trigger] factors@[i as int] <= #[trigger] factors@[j as int]),
    {
        if k % m == 0 {
            proof {
                lemma_first_divisor_is_prime(k as nat, m as nat);
            }
            
            factors.push(m);
            
            proof {
                let old_factors = factors@.drop_last();
                lemma_unfold_right_fold(factors@, old_factors, k, m);
            }
            
            k = k / m;
            
            proof {
                lemma_multiple_mod_is_zero_new(m as int, k as int * m as int, m as int);
            }
        } else {
            m = m + 1;
        }
    }
    
    proof {
        assert(factors@.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == n as nat);
    }
    
    factors
}

} // verus!
fn main() { }