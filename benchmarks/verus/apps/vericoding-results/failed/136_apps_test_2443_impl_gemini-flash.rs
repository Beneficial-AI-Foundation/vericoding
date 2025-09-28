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
/* helper modified by LLM (iteration 5): No helpers. */
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
/* code modified by LLM (iteration 5): Fix `nat` and `int` type errors in concrete code by using `ghost` for verus types. */
{
    // Ghost variables for Verus-specific types
    let ghost n_nat: nat = n as nat;
    let ghost m_nat: nat = m as nat;
    let ghost forbidden_nat: Seq<nat> = forbidden@.map(|_, x: u8| x as nat);

    if m == 1 {
        return (0, Vec::new());
    }

    let mut sequence: Vec<u8> = Vec::new();
    let mut ghost current_product: nat = 1;

    proof {
        assert(prefix_product(sequence@.map(|_, x: u8| x as nat), 0, m_nat) == 1);
    }

    let mut i: nat = 0;
    while i < m_nat
        invariant
            i <= m_nat,
            sequence.len() == i as int,
            current_product == prefix_product(sequence@.map(|_, x: u8| x as nat), i, m_nat),
            sequence@.len() as nat == i,
            (forall|j: int| 0 <= j < i ==> #[trigger] sequence@.map(|_, x: u8| x as nat)[j] < m_nat),
            (forall|j: int| 0 <= j < i ==> #[trigger] sequence@.map(|_, x: u8| x as nat)[j] >= 0),
            all_distinct(sequence@.map(|_, x: u8| x as nat)),
            no_forbidden_products(sequence@.map(|_, x: u8| x as nat), forbidden_nat, m_nat),
            ({
                let current_prefix_products = prefix_products(sequence@.map(|_, x: u8| x as nat), m_nat);
                all_distinct(Seq::new(1, |x: int| 1).add(current_prefix_products))
            }),
            m_nat > 0
        decreases m_nat - i
    {
        let mut found_next_val: bool = false;
        let mut ghost next_val: nat = 0;

        let mut j: nat = 0;
        while j < m_nat
            invariant
                j <= m_nat,
                !found_next_val,
                sequence.len() == i as int,
                current_product == prefix_product(sequence@.map(|_, x: u8| x as nat), i, m_nat),
                sequence@.len() as nat == i,
                (forall|k: int| 0 <= k < i ==> #[trigger] sequence@.map(|_, x: u8| x as nat)[k] < m_nat),
                (forall|k: int| 0 <= k < i ==> #[trigger] sequence@.map(|_, x: u8| x as nat)[k] >= 0),
                all_distinct(sequence@.map(|_, x: u8| x as nat)),
                m_nat > 0,
                no_forbidden_products(sequence@.map(|_, x: u8| x as nat), forbidden_nat, m_nat),
                ({
                    let current_prefix_products = prefix_products(sequence@.map(|_, x: u8| x as nat), m_nat);
                    all_distinct(Seq::new(1, |x: int| 1).add(current_prefix_products))
                }),
                (forall|k: nat| 0 <= k && k < j ==> {
                    let ghost new_product = (prefix_product(sequence@.map(|_, x: u8| x as nat), i, m_nat) * k) % m_nat;
                    let ghost is_not_forbidden = !forbidden_nat.contains(new_product);
                    let ghost is_not_in_sequence = !sequence@.map(|_, x: u8| x as nat).contains(k);
                    let ghost existing_prefix_products = Seq::new(1, |x: int| 1).add(prefix_products(sequence@.map(|_, x: u8| x as nat), m_nat));
                    let ghost is_product_distinct = !existing_prefix_products.contains(new_product);
                    !(is_not_forbidden && is_not_in_sequence && is_product_distinct)
                }) // This ensures that if j increments, the previous values of j were not suitable.
            decreases m_nat - j
        {
            let ghost candidate_val = j;
            let ghost new_product = (prefix_product(sequence@.map(|_, x: u8| x as nat), i, m_nat) * candidate_val) % m_nat;
            let ghost is_not_forbidden = !forbidden_nat.contains(new_product);
            let ghost is_not_in_sequence = !sequence@.map(|_, x: u8| x as nat).contains(candidate_val);
            let ghost existing_prefix_products = Seq::new(1, |x: int| 1).add(prefix_products(sequence@.map(|_, x: u8| x as nat), m_nat));
            let ghost is_product_distinct = !existing_prefix_products.contains(new_product);

            if is_not_forbidden && is_not_in_sequence && is_product_distinct {
                found_next_val = true;
                next_val = candidate_val;
                break;
            }
            j = j + 1;
        }

        if found_next_val {
            sequence.push(next_val as u8);
            current_product = (current_product * next_val) % m_nat;
            i = i + 1;
        } else {
            break;
        }
    }

    proof {
        let ghost final_seq_nat = sequence@.map(|_, x: u8| x as nat);
        if (m_nat > 1) { // Only assert if m_nat > 1 for valid_sequence
            assert(valid_sequence(final_seq_nat, m_nat, forbidden_nat));
        }
    }

    (sequence.len() as u8, sequence)
}
// </vc-code>


}

fn main() {}