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
/* helper modified by LLM (iteration 5): added trigger annotation to fix quantifier inference error */
proof fn lemma_prefix_product_base(s: Seq<nat>, modulus: nat)
    requires modulus > 0
    ensures prefix_product(s, 0, modulus) == 1
{
}

proof fn lemma_prefix_product_step(s: Seq<nat>, i: nat, modulus: nat)
    requires
        modulus > 0,
        i > 0,
        i <= s.len()
    ensures prefix_product(s, i, modulus) == (s[i as int - 1] * prefix_product(s, (i - 1) as nat, modulus)) % modulus
{
}

proof fn lemma_prefix_products_length(s: Seq<nat>, modulus: nat)
    requires modulus > 0
    ensures prefix_products(s, modulus).len() == s.len()
{
}

proof fn lemma_prefix_products_index(s: Seq<nat>, modulus: nat, i: int)
    requires
        modulus > 0,
        0 <= i < s.len()
    ensures prefix_products(s, modulus)[i] == prefix_product(s, (i + 1) as nat, modulus)
{
}

proof fn lemma_all_distinct_empty<T>()
    ensures all_distinct(Seq::<T>::empty())
{
}

proof fn lemma_all_distinct_singleton<T>(x: T)
    ensures all_distinct(seq![x])
{
}

fn compute_prefix_product(s: &Vec<u8>, i: usize, modulus: u8) -> (result: u8)
    requires
        modulus > 0,
        i <= s.len(),
        s@.len() <= 255,
        forall|j: int| 0 <= j < s@.len() ==> s@[j] < modulus
    ensures result == prefix_product(s@.map(|i, x: u8| x as nat), i as nat, modulus as nat) as u8
    decreases i
{
    if i == 0 {
        1
    } else {
        let prev = compute_prefix_product(s, i - 1, modulus);
        ((s[i - 1] as u16 * prev as u16) % modulus as u16) as u8
    }
}

fn vec_contains(v: &Vec<u8>, val: u8) -> (result: bool)
    ensures result == v@.contains(val)
{
    for i in 0..v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j] != val
    {
        if v[i] == val {
            return true;
        }
    }
    false
}

fn check_distinct_products(s: &Vec<u8>, modulus: u8) -> (result: bool)
    requires
        modulus > 0,
        s@.len() <= 255,
        forall|j: int| 0 <= j < s@.len() ==> s@[j] < modulus
    ensures result == all_distinct(Seq::new(1, |x: int| 1).add(prefix_products(s@.map(|i, x: u8| x as nat), modulus as nat)))
{
    let mut seen = Vec::new();
    seen.push(1u8);
    
    for i in 0..s.len()
        invariant
            modulus > 0,
            s@.len() <= 255,
            forall|j: int| 0 <= j < s@.len() ==> s@[j] < modulus,
            i <= s.len(),
            seen.len() == i + 1,
            seen@[0] == 1,
            forall|k: int| 1 <= k < seen@.len() ==> seen@[k] == prefix_product(s@.map(|i, x: u8| x as nat), k as nat, modulus as nat),
            all_distinct(seen@)
    {
        let product = compute_prefix_product(s, i + 1, modulus);
        if vec_contains(&seen, product) {
            return false;
        }
        seen.push(product);
    }
    
    true
}

fn check_no_forbidden(s: &Vec<u8>, forbidden: &Vec<u8>, modulus: u8) -> (result: bool)
    requires
        modulus > 0,
        s@.len() <= 255,
        forall|j: int| 0 <= j < s@.len() ==> s@[j] < modulus
    ensures result == no_forbidden_products(s@.map(|i, x: u8| x as nat), forbidden@.map(|i, x: u8| x as nat), modulus as nat)
{
    for i in 0..s.len()
        invariant
            modulus > 0,
            s@.len() <= 255,
            forall|j: int| 0 <= j < s@.len() ==> s@[j] < modulus,
            i <= s.len(),
            forall|k: int| 0 <= k < i ==> !forbidden@.map(|i, x: u8| x as nat).contains(#[trigger] prefix_product(s@.map(|i, x: u8| x as nat), (k + 1) as nat, modulus as nat))
    {
        let product = compute_prefix_product(s, i + 1, modulus);
        if vec_contains(forbidden, product) {
            return false;
        }
    }
    
    true
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
    /* code modified by LLM (iteration 5): same implementation as previous iteration */
    if m == 1 {
        return (0, Vec::new());
    }
    
    let mut sequence = Vec::new();
    
    // Simple greedy approach: try to build a sequence by choosing the first valid element
    for _len in 0..m {
        let mut found_next = false;
        
        for candidate in 0..m {
            sequence.push(candidate);
            
            if check_distinct_products(&sequence, m) && check_no_forbidden(&sequence, &forbidden, m) {
                found_next = true;
                break;
            }
            
            sequence.pop();
        }
        
        if !found_next {
            break;
        }
    }
    
    (sequence.len() as u8, sequence)
}
// </vc-code>


}

fn main() {}