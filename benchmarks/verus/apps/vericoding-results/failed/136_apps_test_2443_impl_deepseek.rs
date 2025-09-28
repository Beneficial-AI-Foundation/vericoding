// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn prefix_product(s: Seq<nat>, i: nat, modulus: nat) -> nat
  recommends modulus > 0, i <= s.len()
  decreases i
{
    if i == 0 { 1 }
    else { (s[i as int - 1] * prefix_product(s, (i - 1) as nat, modulus)) % modulus }
}

spec fn prefix_products(s: Seq<nat>, modulus: nat) -> Seq<nat>
  recommends modulus > 0
{
    Seq::new(s.len(), |i: int| prefix_product(s, (i + 1) as nat, modulus))
}

spec fn all_distinct<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

spec fn no_forbidden_products(s: Seq<nat>, forbidden: Seq<nat>, modulus: nat) -> bool
  recommends modulus > 0
{
    let products = prefix_products(s, modulus);
    forall|i: int| 0 <= i < products.len() ==> !forbidden.contains(products[i])
}

spec fn valid_input(n: nat, m: nat, forbidden: Seq<nat>) -> bool {
    m >= 1 &&
    n >= 0 &&
    forbidden.len() == n &&
    (forall|i: int| 0 <= i < forbidden.len() ==> #[trigger] forbidden[i] >= 0 && forbidden[i] < m) &&
    (forall|i: int, j: int| 0 <= i < j < forbidden.len() ==> #[trigger] forbidden[i] != #[trigger] forbidden[j])
}

spec fn valid_sequence(sequence: Seq<nat>, m: nat, forbidden: Seq<nat>) -> bool
  recommends m > 0
{
    (forall|i: int| 0 <= i < sequence.len() ==> #[trigger] sequence[i] >= 0 && sequence[i] < m) &&
    all_distinct(Seq::new(1, |x: int| 1).add(prefix_products(sequence, m))) &&
    no_forbidden_products(sequence, forbidden, m)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix compilation errors and verification */
proof fn prefix_product_decreases(s: Seq<nat>, i: nat, modulus: nat) 
    requires modulus > 0
    ensures prefix_product(s, i, modulus) >= 0 && prefix_product(s, i, modulus) < modulus
    decreases i
{
    if i == 0 {
        assert(prefix_product(s, i, modulus) == 1) by {
            reveal_with_fuel(prefix_product, 2);
        };
        assert(1 >= 0 && 1 < modulus) by {
            assert(modulus > 0);
        };
    } else {
        assert(0 < i && i <= s.len()) by {
            assert(i > 0);
        };
        let prev = prefix_product(s, (i - 1) as nat, modulus);
        prefix_product_decreases(s, (i - 1) as nat, modulus);
        assert(prev >= 0 && prev < modulus);
        assert(s[i as int - 1] >= 0 && s[i as int - 1] < modulus) by {
            if (i as int - 1) < s.len() as int {
                assert(s[i as int - 1] >= 0);
            }
        };
        assert((s[i as int - 1] * prev) % modulus >= 0);
        assert((s[i as int - 1] * prev) % modulus < modulus);
    }
}

proof fn all_distinct_prefix_products_step(sequence: Seq<nat>, i: nat, modulus: nat)
    requires
        modulus > 0,
        all_distinct(Seq::new((sequence.len() + 1) as nat, |j: int| 
            if j == 0 { 1 } else { prefix_product(sequence, j as nat, modulus) }
        )),
    ensures
        all_distinct(Seq::new((i + 1) as nat, |j: int| 
            if j == 0 { 1 } else { prefix_product(sequence.subrange(0, i as int), j as nat, modulus) }
        ))
    decreases i
{
    if i > 0 {
        all_distinct_prefix_products_step(sequence, (i - 1) as nat, modulus);
    }
}

proof fn no_forbidden_prefix_products_step(sequence: Seq<nat>, forbidden: Seq<nat>, i: nat, modulus: nat)
    requires
        modulus > 0,
        no_forbidden_products(sequence, forbidden, modulus),
    ensures
        no_forbidden_products(sequence.subrange(0, i as int), forbidden, modulus)
    decreases i
{
    if i > 0 {
        no_forbidden_prefix_products_step(sequence, forbidden, (i - 1) as nat, modulus);
    }
}

spec fn contains_forbidden(forbidden: Seq<nat>, value: nat) -> bool {
    exists|i: int| 0 <= i < forbidden.len() && forbidden[i] == value
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, m: u8, forbidden: Vec<u8>) -> (result: (u8, Vec<u8>))
  requires valid_input(n as nat, m as nat, forbidden@.map(|i, x: u8| x as nat))
  ensures ({
      let (length, sequence) = result;
      length == sequence.len() as u8 &&
      length >= 0 &&
      (m == 1 ==> length == 0 && sequence@ == Seq::<u8>::empty()) &&
      (m > 1 ==> valid_sequence(sequence@.map(|i, x: u8| x as nat), m as nat, forbidden@.map(|i, x: u8| x as nat))) &&
      (n == 0 && m > 1 ==> length > 0)
  })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix compilation errors by replacing contains with manual check */
    if m == 1 {
        return (0, Vec::new());
    }
    
    let mut result_vec = Vec::new();
    let mut used = Vec::with_capacity(m as usize);
    for _ in 0..m {
        used.push(false);
    }
    
    let mut current_product: u8 = 1;
    
    for _ in 0..n {
        let mut found = false;
        
        for candidate in 1..m {
            if used[candidate as usize] {
                continue;
            }
            
            let mut is_forbidden = false;
            for i in 0..forbidden.len() {
                if forbidden[i] == candidate {
                    is_forbidden = true;
                    break;
                }
            }
            if is_forbidden {
                continue;
            }
            
            let new_product = (current_product.wrapping_mul(candidate)) % m;
            if new_product == 0 {
                continue;
            }
            
            let mut new_product_forbidden = false;
            for i in 0..forbidden.len() {
                if forbidden[i] == new_product {
                    new_product_forbidden = true;
                    break;
                }
            }
            if new_product_forbidden {
                continue;
            }
            
            result_vec.push(candidate);
            used[candidate as usize] = true;
            current_product = new_product;
            found = true;
            break;
        }
        
        if !found {
            break;
        }
    }
    
    (result_vec.len() as u8, result_vec)
}
// </vc-code>


}

fn main() {}