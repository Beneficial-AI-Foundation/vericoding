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
    // impl-start
    if seq.len() == 0 {
    } else {
        calc! {
            (==)
            seq.fold_right(|x, acc: nat| (acc * x) as nat, k); {
                lemma_fold_right_pull_out_nat(seq.drop_last(), (k * seq.last()) as nat)
            }
            (seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * (k
                * seq.last()) as nat) as nat; {
                lemma_mul_is_commutative(k as int, seq.last() as int)
            }
            (seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * (seq.last()
                * k) as nat) as nat; {
                lemma_mul_is_associative(
                    seq.drop_last().fold_right(|x: nat, acc: nat| (acc * x) as nat, 1nat) as int,
                    seq.last() as int,
                    k as int,
                );
            }  
            (((seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * seq.last()) as nat)
                * k) as nat; { lemma_fold_right_pull_out_nat(seq.drop_last(), seq.last() as nat) }
            (seq.fold_right(|x, acc: nat| (acc * x) as nat, 1) * k) as nat;
        }
    }
    // impl-end
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
    // impl-start
    if seq.len() == 0 {
    } else {
        calc! {
            (==)
            seq.fold_right(|x, acc: nat| (acc * x) as nat, k); {
                lemma_fold_right_pull_out_hybrid(seq.drop_last(), (k * seq.last()) as nat)
            }
            (seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * (k
                * seq.last()) as nat) as nat; {
                lemma_mul_is_commutative(k as int, seq.last() as int)
            }
            (seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * (seq.last()
                * k) as nat) as nat; {
                lemma_mul_is_associative(
                    seq.drop_last().fold_right(|x: u8, acc: nat| (acc * x) as nat, 1nat) as int,
                    seq.last() as int,
                    k as int,
                );
            }
            (((seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * seq.last()) as nat)
                * k) as nat; { lemma_fold_right_pull_out_hybrid(seq.drop_last(), seq.last() as nat)
            }
            (seq.fold_right(|x, acc: nat| (acc * x) as nat, 1) * k) as nat;
        }
    }
    // impl-end
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
    // impl-start
    assert((old_factors.push(m)).drop_last() == old_factors);
    assert(((k as int) / (m as int)) * (m as int) + (k as int) % (m as int) == (k as int)) by {
        lemma_fundamental_div_mod(k as int, m as int)
    };
    // impl-end
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
    // impl-start
    assert((old_factors.push(m as u8)).drop_last() == old_factors);
    assert(factors.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == old_factors.fold_right(
        |x, acc: nat| (acc * x) as nat,
        1,
    ) * (m as nat)) by { lemma_fold_right_pull_out_hybrid(old_factors, m as nat) }
    // impl-end
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
    // impl-start
    assert(k == (k / m) * m) by { lemma_fundamental_div_mod(k, m) };
    assert(n == (n / k) * k) by { lemma_fundamental_div_mod(n, k) };

    assert(n == ((n / k) * m) * (k / m)) by {
        broadcast use group_mul_properties;

    };
    assert(n % (k / m) == 0) by { lemma_mod_multiples_basic((n / k) * m, k / m) };
    // impl-end
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
    // impl-start
    assert(k == (k / m) * m) by { lemma_fundamental_div_mod(k, m) };
    let a = choose|a: int| (#[trigger] (a * m) == k && (a == k / m));

    assert(n == (n / k) * k) by { lemma_fundamental_div_mod(n, k) };
    let b = choose|b: int| (#[trigger] (b * k) == n && b == n / k);

    assert((a * m) * b == n) by { lemma_mul_is_commutative(b, a * m) }
    assert(a * (m * b) == n) by { lemma_mul_is_associative(a, m, b) };
    assert((m * b) == n / a) by { lemma_div_multiples_vanish(m * b, a) };
    // impl-end
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
    // impl-start
    assert_by_contradiction!((k/m) % j != 0,
        {
            assert (k == (k/m) * m) by {lemma_fundamental_div_mod(k, m)};
            let a = choose|a:int| (#[trigger] (a * m) == k);

            assert ((k/m) == ((k/m)/j) * j) by {lemma_fundamental_div_mod(k/m, j)};
            let b = choose|b:int| (#[trigger] (b * j) == k/m);

            calc! {
                (==)
                k % j; {broadcast use group_mul_properties;}
                ((b * m) * j) % j; {broadcast use lemma_mod_multiples_basic;}
                0;
            }
        });
    // impl-end
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
    // impl-start
    assert(k == (k / m) * m) by { lemma_fundamental_div_mod(k as int, m as int) };
    let a = choose|a: int| (#[trigger] (a * m) == k);

    assert(m == (m / i) * i) by { lemma_fundamental_div_mod(m as int, i as int) };
    let b = choose|b: int| (#[trigger] (b * i) == m);

    assert(k == (a * b) * i) by { lemma_mul_is_associative(a, b, i) };
    assert(k % i == 0) by { lemma_mod_multiples_vanish(a * b, 0, i) };
    // impl-end

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
    // impl-start
    assert_by_contradiction!(is_prime(m),
        {
            let i = choose|i:nat| (1 < i < m && #[trigger] (m % i) == 0);
            assert (k % i == 0) by {lemma_mod_zero_twice(k as int, m as int, i as int)};
        })
    // impl-end
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
    // impl-start
    assert(seq.map(|_idx, j: u8| j as nat).drop_last() == seq.drop_last().map(
        |_idx, j: u8| j as nat,
    ));
    // impl-end
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
    // impl-start
    if (factorization.len() == 0) {
    } else {
        let factorization_ = factorization.drop_last();
        let last = factorization.last();

        calc! {
            (==)
            factorization.map(|_idx, j: u8| j as nat).fold_right(|x, acc: nat| acc * x, 1nat); {
                lemma_drop_last_map_commute(factorization)
            }
            factorization.drop_last().map(|_idx, j: u8| j as nat).fold_right(
                |x, acc: nat| acc * x,
                (factorization.last() as nat),
            ); {
                lemma_fold_right_pull_out_nat(
                    factorization.drop_last().map(|_idx, j: u8| j as nat),
                    (factorization.last() as nat),
                )
            }
            factorization.drop_last().map(|_idx, j: u8| j as nat).fold_right(
                |x, acc: nat| acc * x,
                1nat,
            ) * (factorization.last() as nat); {
                lemma_fold_right_equivalent_for_nat_u8(factorization.drop_last())
            }
            factorization.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1nat) * (
            factorization.last() as nat); {
                lemma_fold_right_pull_out_hybrid(
                    factorization.drop_last(),
                    (factorization.last() as nat),
                )
            }
            factorization.drop_last().fold_right(
                |x, acc: nat| (acc * x) as nat,
                (factorization.last() as nat),
            );
        }
    }
    // impl-end
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
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!
fn main() { }