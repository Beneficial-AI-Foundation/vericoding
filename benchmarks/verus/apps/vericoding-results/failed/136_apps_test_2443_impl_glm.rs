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
/* helper modified by LLM (iteration 3): Remove early return and use found variable */
fn contains_forbidden(forbidden: &Vec<u8>, value: u8) -> (result: bool)
    ensures result == exists|i: int| 0 <= i < forbidden.len() && forbidden[i] == value
{
    let mut found = false;
    let mut i = 0;
    while i < forbidden.len()
        invariant
            0 <= i <= forbidden.len(),
            found ==> (exists|j: int| 0 <= j < i && forbidden[j] == value),
            !found ==> (forall|j: int| 0 <= j < i ==> forbidden[j] != value)
    {
        if !found && forbidden[i] == value {
            found = true;
        }
        i += 1;
    }
    found
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
/* code modified by LLM (iteration 2): Replace forbidden.contains() with helper function */
{
    if m == 1 {
        return (0, Vec::new());
    } else if n == 0 {
        let mut seq = Vec::new();
        seq.push(0);
        return (1, seq);
    } else {
        for x in 0..m {
            if x != 1 && !contains_forbidden(&forbidden, x) {
                let mut seq = Vec::new();
                seq.push(x);
                return (1, seq);
            }
        }
        return (0, Vec::new());
    }
}
// </vc-code>


}

fn main() {}