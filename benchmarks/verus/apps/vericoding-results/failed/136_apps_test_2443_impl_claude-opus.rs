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
proof fn lemma_prefix_product_bounds(s: Seq<nat>, i: nat, modulus: nat)
    requires
        modulus > 0,
        i <= s.len(),
        forall|j: int| 0 <= j < s.len() ==> s[j] < modulus,
    ensures
        prefix_product(s, i, modulus) < modulus,
    decreases i
{
    if i == 0 {
    } else {
        lemma_prefix_product_bounds(s, (i - 1) as nat, modulus);
    }
}

proof fn lemma_prefix_product_positive(s: Seq<nat>, i: nat, modulus: nat)
    requires
        modulus > 0,
        i <= s.len(),
        forall|k: int| 0 <= k < s.len() ==> s[k] > 0,
    ensures
        prefix_product(s, i, modulus) > 0,
    decreases i
{
    if i == 0 {
    } else {
        lemma_prefix_product_positive(s, (i - 1) as nat, modulus);
    }
}

fn vec_contains(v: &Vec<u8>, val: u8) -> (found: bool)
    ensures
        found <==> v@.contains(val),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i ==> v[j as int] != val,
        decreases v.len() - i
    {
        if v[i] == val {
            return true;
        }
        i = i + 1;
    }
    false
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
    /* code modified by LLM (iteration 5): Added trigger annotations to quantifier */
    if m == 1 {
        return (0, Vec::new());
    }
    
    let mut sequence: Vec<u8> = Vec::new();
    let mut used_products: Vec<u8> = Vec::new();
    used_products.push(1u8);
    
    let mut current_product: u8 = 1;
    
    while sequence.len() < 255 && sequence.len() < (m - 1) as usize
        invariant
            m > 1,
            valid_input(n as nat, m as nat, forbidden@.map(|i, x: u8| x as nat)),
            sequence.len() <= 255,
            sequence.len() < m as usize,
            used_products.len() == sequence.len() + 1,
            used_products[0] == 1,
            forall|i: int| 0 <= i < sequence.len() ==> sequence[i as int] < m,
            forall|i: int| 0 <= i < sequence.len() ==> sequence[i as int] > 0,
            current_product < m,
            current_product == if sequence.len() == 0 { 1 } else { prefix_product(sequence@.map(|j, x: u8| x as nat), sequence.len() as nat, m as nat) as u8 },
            forall|i: int| 0 <= i < used_products.len() ==> used_products[i as int] < m,
            forall|i: int| 1 <= i < used_products.len() ==> used_products[i as int] == prefix_product(sequence@.map(|j, x: u8| x as nat), i as nat, m as nat),
            forall|i: int, j: int| 0 <= i < j < used_products.len() ==> used_products[i as int] != used_products[j as int],
            forall|i: int| 0 <= i < used_products.len() ==> !forbidden@.map(|j, x: u8| x as nat).contains(used_products[i as int] as nat),
        decreases (m - 1) as usize - sequence.len()
    {
        let mut next_val: u8 = 1;
        let mut found = false;
        
        while next_val < m && !found
            invariant
                m > 1,
                next_val <= m,
                next_val >= 1,
                sequence.len() < 255,
                sequence.len() < m as usize,
                current_product < m,
                !found ==> forall|k: int| 1 <= k < next_val ==> {
                    let new_prod = ((k * current_product as int) % (m as int)) as nat;
                    #[trigger] forbidden@.map(|j, x: u8| x as nat).contains(new_prod) ||
                    #[trigger] used_products@.map(|j, x: u8| x as nat).contains(new_prod)
                },
            decreases m - next_val
        {
            let new_product = ((next_val as u32 * current_product as u32) % (m as u32)) as u8;
            
            let forbidden_contains = vec_contains(&forbidden, new_product);
            let used_contains = vec_contains(&used_products, new_product);
            
            if !forbidden_contains && !used_contains {
                found = true;
                sequence.push(next_val);
                used_products.push(new_product);
                current_product = new_product;
            } else {
                next_val = next_val + 1;
            }
        }
        
        if !found {
            break;
        }
    }
    
    let length = sequence.len() as u8;
    (length, sequence)
}
// </vc-code>


}

fn main() {}