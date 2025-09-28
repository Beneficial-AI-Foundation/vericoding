// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * int_pow(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_pow_zero(base: int)
    ensures int_pow(base, 0) == 1,
{
}

proof fn lemma_pow_rec(base: int, exp: nat)
    requires exp > 0,
    ensures int_pow(base, exp) == base * int_pow(base, (exp - 1) as nat),
{
}

spec fn vec_to_seq<T>(v: Vec<T>) -> Seq<T>;

proof fn lemma_vec_len<T>(v: Vec<T>)
    ensures v@.len() == v.len(),
{
}

proof fn lemma_vec_index<T>(v: Vec<T>, i: int)
    requires 0 <= i < v@.len(),
    ensures v@[i] == v[i as usize],
{
}

// </vc-helpers>

// <vc-spec>
fn power(a: Vec<i8>, b: Vec<u8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == int_pow(a@[i] as int, b@[i] as nat),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let len = a.len();
    let mut i = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == int_pow(a@[j] as int, b@[j] as nat),
    {
        let base = a[i] as int;
        let exp = b[i] as nat;
        let mut pow_result = 1;
        let mut exp_counter = 0;
        
        while exp_counter < exp
            invariant
                0 <= exp_counter <= exp,
                pow_result == int_pow(base, exp_counter),
        {
            pow_result = pow_result * base;
            exp_counter = exp_counter + 1;
        }
        
        result.push(pow_result as i8);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}