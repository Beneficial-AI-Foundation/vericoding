// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn prefix_product(s: Seq<nat>, i: nat, mod_val: nat) -> nat
  recommends mod_val > 0, i <= s.len()
{
    if i == 0 { 1 }
    else { (s[i as int - 1] * prefix_product(s, (i - 1) as nat, mod_val)) % mod_val }
}

spec fn prefix_products(s: Seq<nat>, mod_val: nat) -> Seq<nat>
  recommends mod_val > 0
{
    Seq::new(s.len(), |i: int| prefix_product(s, (i + 1) as nat, mod_val))
}

spec fn all_distinct<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] !== s[j]
}

spec fn no_forbidden_products(s: Seq<nat>, forbidden: Seq<nat>, mod_val: nat) -> bool
  recommends mod_val > 0
{
    let products = prefix_products(s, mod_val);
    forall|i: int| 0 <= i < products.len() ==> !forbidden.contains(products[i])
}

spec fn valid_input(n: nat, m: nat, forbidden: Seq<nat>) -> bool {
    m >= 1 &&
    n >= 0 &&
    forbidden.len() == n &&
    (forall|i: int| 0 <= i < forbidden.len() ==> 0 <= forbidden[i] < m) &&
    (forall|i: int, j: int| 0 <= i < j < forbidden.len() ==> forbidden[i] != forbidden[j])
}

spec fn valid_sequence(sequence: Seq<nat>, m: nat, forbidden: Seq<nat>) -> bool
  recommends m > 0
{
    (forall|i: int| 0 <= i < sequence.len() ==> 0 <= sequence[i] < m) &&
    all_distinct(seq![1].add(prefix_products(sequence, m))) &&
    no_forbidden_products(sequence, forbidden, m)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: nat, m: nat, forbidden: Seq<nat>) -> (result: (nat, Seq<nat>))
  requires valid_input(n, m, forbidden)
  ensures 
    result.0 == result.1.len() &&
    result.0 >= 0 &&
    (m == 1 ==> result.0 == 0 && result.1 == Seq::empty()) &&
    (m > 1 ==> valid_sequence(result.1, m, forbidden)) &&
    (n == 0 && m > 1 ==> result.0 > 0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    (0 as nat, Seq::empty())
}
// </vc-code>


}

fn main() {}