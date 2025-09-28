use vstd::prelude::*;

verus! {

// recursive definition of factorial
spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// iterative implementation of factorial

// <vc-helpers>
spec fn prod_seq(s: Seq<u32>, i: int, j: int) -> u32
    decreases j - i,
{
    if i >= j {
        1
    } else {
        (s[i] as u64) * (prod_seq(s, i + 1, j) as u64) as u32
    }
}

proof fn prod_seq_split(s: Seq<u32>, i: int, k: int, j: int)
    requires
        i <= k <= j,
    ensures
        prod_seq(s, i, j) == prod_seq(s, i, k) * prod_seq(s, k, j),
    decreases j - i,
{
    if i < k {
        prod_seq_split(s, i + 1, k, j);
    }
}

proof fn prod_seq_update(s1: Seq<u32>, s2: Seq<u32>, i: int)
    requires
        i >= 0,
        s1 =~= s2,
        forall|k: int| 0 <= k && k < s1.len() && k != i ==> s1[k] == s2[k],
    ensures
        prod_seq(s1, 0, s1.len() as int) == prod_seq(s2, 0, s2.len() as int),
{
    if s1.len() > 0 {
        if i == 0 {
            prod_seq_split(s1, 0, 1, s1.len() as int);
            prod_seq_split(s2, 0, 1, s2.len() as int);
        } else {
            prod_seq_split(s1, 0, i, s1.len() as int);
            prod_seq_split(s2, 0, i, s2.len() as int);
            prod_seq_split(s1, i, i+1, s1.len() as int);
            prod_seq_split(s2, i, i+1, s2.len() as int);
        }
    }
}

proof fn factorial_property(n: nat)
    ensures factorial(n) == if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
{
    if n > 0 {
        assert(factorial(n) == n * factorial((n - 1) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13, // prevent overflow
    ensures result == factorial(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut result: u32 = 1;
    let mut i: u32 = 0;
    let mut vec = Vec::new();
    vec.push(1);
    
    while i < n
        invariant
            i <= n,
            vec.len() == (i + 1) as usize,
            forall|k: int| 0 <= k && k < vec.len() ==> #[trigger] vec@[k] == factorial(k as nat),
            result == vec@[i as int] == factorial(i as nat),
    {
        i = i + 1;
        let new_val = (result as u64 * i as u64) as u32;
        proof {
            factorial_property(i as nat);
        }
        vec.push(new_val);
        result = new_val;
        proof {
            assert(vec@[i as int] == factorial(i as nat)) by {
                assert(vec@[i as int] == new_val);
            };
        }
    }
    result
}
// </vc-code>

fn main() {}

}