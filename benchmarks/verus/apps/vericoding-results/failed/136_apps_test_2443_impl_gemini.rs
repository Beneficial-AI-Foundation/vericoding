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
proof fn lemma_prefix_product_properties(s1: Seq<nat>, s2: Seq<nat>, i: nat, m: nat)
    requires
        m > 0,
        i <= s1.len(),
        i <= s2.len(),
        s1.take(i) == s2.take(i),
    ensures
        prefix_product(s1, i, m) == prefix_product(s2, i, m),
    decreases i
{
    if i > 0 {
        lemma_prefix_product_properties(s1, s2, (i - 1) as nat, m);
    }
}

proof fn lemma_prefix_product_snoc(s: Seq<nat>, x: nat, m: nat)
    requires m > 0
    ensures prefix_product(s.push(x), s.len() + 1, m) == (x * prefix_product(s, s.len(), m)) % m,
{
    lemma_prefix_product_properties(s.push(x), s, s.len() as nat, m);
}

/* helper modified by LLM (iteration 2): fixed syntax error ('implies' -> '==>') */
proof fn lemma_prefix_products_snoc(s: Seq<nat>, x: nat, m: nat)
    requires m > 0
    ensures
        prefix_products(s.push(x), m).len() == s.len() + 1,
        prefix_products(s.push(x), m).take(s.len()) == prefix_products(s, m),
        prefix_products(s.push(x), m).last() == (x * prefix_product(s, s.len(), m)) % m,
{
    let s_new = s.push(x);
    let prods_new = prefix_products(s_new, m);
    let prods_old = prefix_products(s, m);
    assert forall|i: int| 0 <= i < s.len() ==> prods_new[i] == prods_old[i] by {
        lemma_prefix_product_properties(s_new, s, (i + 1) as nat, m);
    };
    assert(prods_new.take(s.len()) == prods_old);
    lemma_prefix_product_snoc(s, x, m);
}

/* helper modified by LLM (iteration 2): fixed syntax error ('implies' -> '==>') */
proof fn lemma_all_distinct_snoc<T>(s: Seq<T>, x: T)
    requires
        all_distinct(s),
        !s.contains(x),
    ensures
        all_distinct(s.push(x)),
    {
        let s_new = s.push(x);
        assert forall|i: int, j: int| 0 <= i < j < s_new.len() ==> s_new[i] != s_new[j] by {
            if j < s.len() {
                assert(s[i] != s[j]);
            } else {
                assert(s[i] != x);
            }
        };
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
    /* code modified by LLM (iteration 2): added comment */
    if m == 1 {
        let empty_vec = Vec::new();
        return (0, empty_vec);
    }

    let m_nat = m as nat;
    let forbidden_nat = forbidden@.map(|i, x: u8| x as nat);

    let mut used = Vec::new_with_len(m as usize, false);
    let mut i: usize = 0;
    while i < forbidden.len()
        invariant
            used.len() == m as usize,
            i <= forbidden.len(),
            forall|j: int| 0 <= j < i ==> used[forbidden[j] as int],
            forall|j: int, k: int| 0 <= j < k < i ==> forbidden[j] != forbidden[k],
            forall|j: int| 0 <= j < i ==> forbidden[j] < m,
        decreases forbidden.len() - i
    {
        let f = forbidden[i] as usize;
        used.set(f, true);
        i += 1;
    }
    used.set(1, true);

    let mut sequence = Vec::<u8>::new();
    let mut current_prod: u8 = 1;

    loop
        invariant
            m > 1,
            used.len() == m_nat,
            valid_input(n as nat, m_nat, forbidden_nat),
            current_prod as nat == prefix_product(sequence@.map(|_i,x|x as nat), sequence.len() as nat, m_nat),
            valid_sequence(sequence@.map(|_i, x| x as nat), m_nat, forbidden_nat),
            
            forall|p: nat| p < m_nat ==> (used[p as int] <==> (
                p == 1 ||
                forbidden_nat.contains(p) ||
                prefix_products(sequence@.map(|_i, x| x as nat), m_nat).contains(p)
            )),
        decreases m_nat - sequence.len() as nat
    {
        let mut found_s: Option<u8> = None;
        let mut next_s_iter: u8 = 0;
        while next_s_iter < m
            invariant
                next_s_iter <= m,
                found_s.is_None() <==> forall|s_val: u8| s_val < next_s_iter ==> used[((s_val as u64 * current_prod as u64) % (m as u64)) as usize],
            decreases m - next_s_iter
        {
            let next_prod = (next_s_iter as u64 * current_prod as u64) % (m as u64);
            if !used[next_prod as usize] {
                found_s = Some(next_s_iter);
                break;
            }
            next_s_iter += 1;
        }

        if let Some(s) = found_s {
            proof {
                let seq_nat = sequence@.map(|_i, x| x as nat);
                let s_nat = s as nat;
                let new_seq_nat = seq_nat.push(s_nat);
                let next_prod_nat = (s_nat * current_prod as nat) % m_nat;

                let old_prods_with_1 = Seq::new(1, |_| 1 nat).add(prefix_products(seq_nat, m_nat));
                lemma_all_distinct_snoc::<nat>(old_prods_with_1, next_prod_nat);
                lemma_prefix_products_snoc(seq_nat, s_nat, m_nat);
            }
            sequence.push(s);
            current_prod = ((s as u64 * current_prod as u64) % (m as u64)) as u8;
            used.set(current_prod as usize, true);
        } else {
            break;
        }
    }

    (sequence.len() as u8, sequence)
}
// </vc-code>


}

fn main() {}