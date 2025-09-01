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

// <vc-helpers>
proof fn lemma_prime_factorization_empty()
    ensures is_prime_factorization(1, Seq::<nat>::empty())
{
    assert(Seq::<nat>::empty().fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat) == 1);
}

proof fn lemma_prime_factorization_extend(n: nat, m: nat, factorization: Seq<nat>)
    requires 
        is_prime_factorization(n, factorization),
        is_prime(m),
        factorization.len() == 0 || factorization[factorization.len() - 1] <= m,
    ensures
        is_prime_factorization(n * m, factorization.push(m))
{
    let extended = factorization.push(m);
    assert(extended.fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat) == n * m) by {
        assert(extended.fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat) 
               == factorization.fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat) * m);
    };
}

proof fn lemma_is_prime_2()
    ensures is_prime(2)
{
    assert(forall|i: nat| 1 < i < 2 ==> #[trigger] (2 % i) != 0) by {
        assert(forall|i: nat| 1 < i < 2 ==> false);
    };
}

proof fn lemma_smallest_factor_is_prime(n: nat) -> (result: nat)
    requires n >= 2
    ensures 
        2 <= result <= n,
        n % result == 0,
        is_prime(result),
    decreases n
{
    if n == 2 {
        lemma_is_prime_2();
        2
    } else {
        let mut i = 2;
        while i * i <= n
            invariant 
                2 <= i <= n,
                forall|j: nat| 2 <= j < i ==> #[trigger] (n % j) != 0,
        {
            if n % i == 0 {
                assert(is_prime(i)) by {
                    assert(forall|k: nat| 1 < k < i ==> #[trigger] (i % k) != 0);
                };
                return i;
            }
            i = i + 1;
        }
        assert(is_prime(n)) by {
            assert(forall|j: nat| 1 < j < n ==> #[trigger] (n % j) != 0);
        };
        n
    }
}
// </vc-helpers>

// <vc-spec>
fn factorize(n: u8) -> (factorization: Vec<u8>)
    // pre-conditions-start
    requires
        1 <= n <= u8::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_prime_factorization(n as nat, factorization@.map(|_idx, j: u8| j as nat)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if n == 1 {
        proof { lemma_prime_factorization_empty(); }
        return vec![];
    }
    
    let mut result = Vec::new();
    let mut remaining = n as nat;
    
    while remaining > 1
        invariant
            remaining >= 1,
            is_prime_factorization(
                (n as nat) / remaining, 
                result@.map(|_idx, j: u8| j as nat)
            ),
            result@.len() == 0 || forall|i: int| 0 <= i < result@.len() ==> result@[i] <= u8::MAX,
    {
        proof {
            let factor = lemma_smallest_factor_is_prime(remaining);
            assert(factor <= remaining <= u8::MAX);
        }
        
        let mut factor = 2u8;
        while factor as nat * factor as nat <= remaining && remaining % (factor as nat) != 0
            invariant
                2 <= factor <= u8::MAX,
                forall|j: nat| 2 <= j < factor ==> #[trigger] (remaining % j) != 0,
        {
            factor = factor + 1;
        }
        
        if remaining % (factor as nat) != 0 {
            factor = remaining as u8;
        }
        
        result.push(factor);
        remaining = remaining / (factor as nat);
        
        proof {
            lemma_prime_factorization_extend(
                (n as nat) / (remaining * (factor as nat)),
                factor as nat,
                old(result)@.map(|_idx, j: u8| j as nat)
            );
        }
    }
    
    result
}
// </vc-code>

} // verus!
fn main() { }