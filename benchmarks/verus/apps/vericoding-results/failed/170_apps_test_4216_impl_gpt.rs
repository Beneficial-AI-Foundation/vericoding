// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn num_digits(n: int) -> int
  recommends n >= 1
  decreases n
{
  if n < 10 { 1 } else { 1 + num_digits(n / 10) }
}

spec fn valid_input(n: int) -> bool {
  n >= 1
}

spec fn f(a: int, b: int) -> int
  recommends a >= 1 && b >= 1
{
  let digits_a = num_digits(a);
  let digits_b = num_digits(b);
  if digits_a > digits_b { digits_a } else { digits_b }
}

spec fn is_factor_pair(a: int, b: int, n: int) -> bool {
  a >= 1 && b >= 1 && a * b == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): exact values of num_digits for 1..=9 */
proof fn lemma_num_digits_1_to_9(n: int)
    requires
        1 <= n,
        n <= 9,
    ensures
        num_digits(n) == 1,
{
    assert(num_digits(n) == 1);
}

/* helper modified by LLM (iteration 2): exact values of num_digits for 10..=99 */
proof fn lemma_num_digits_10_to_99(n: int)
    requires
        10 <= n,
        n <= 99,
    ensures
        num_digits(n) == 2,
{
    let q = n / 10;
    assert(1 <= q);
    assert(q <= 9);
    lemma_num_digits_1_to_9(q);
    assert(num_digits(q) == 1);
    assert(num_digits(n) == 1 + num_digits(q));
    assert(num_digits(n) == 2);
}

/* helper modified by LLM (iteration 2): exact values of num_digits for 100..=127 */
proof fn lemma_num_digits_100_to_127(n: int)
    requires
        100 <= n,
        n <= 127,
    ensures
        num_digits(n) == 3,
{
    let q = n / 10;
    assert(10 <= q);
    assert(q <= 12);
    lemma_num_digits_10_to_99(q);
    assert(num_digits(q) == 2);
    assert(num_digits(n) == 1 + num_digits(q));
    assert(num_digits(n) == 3);
}

/* helper modified by LLM (iteration 2): runtime digits for i8 with proof it matches spec */
fn digits_i8(x: i8) -> (res: i8)
    requires
        1 <= x as int,
    ensures
        res as int == num_digits(x as int),
{
    if x < 10 {
        proof {
            let xi = x as int;
            assert(1 <= xi);
            assert(xi <= 9);
            lemma_num_digits_1_to_9(xi);
        }
        1
    } else if x < 100 {
        proof {
            let xi = x as int;
            assert(10 <= xi);
            assert(xi <= 99);
            lemma_num_digits_10_to_99(xi);
        }
        2
    } else {
        proof {
            let xi = x as int;
            assert(100 <= xi);
            assert(xi <= 127);
            lemma_num_digits_100_to_127(xi);
        }
        3
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires 
    valid_input(n as int)
  ensures 
    result >= 1,
    exists|a: int, b: int| is_factor_pair(a, b, n as int) && result as int == f(a, b),
    forall|a: int, b: int| is_factor_pair(a, b, n as int) ==> result as int <= f(a, b),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented executable search over divisors with i8 and ghost proofs tying to specs */
  let ghost N: int = n as int;

  // initialize best with pair (1, n)
  let mut i: i8 = 1;
  let mut besta: i8 = 1;
  let mut bestb: i8 = n;
  let d1 = digits_i8(1);
  let d2 = digits_i8(n);
  let mut best: i8 = if d1 > d2 { d1 } else { d2 };

  proof {
      assert(1 <= (besta as int));
      assert(1 <= (bestb as int));
      assert((besta as int) * (bestb as int) == N);
      let da: int = digits_i8(besta) as int;
      let db: int = digits_i8(bestb) as int;
      assert(da == num_digits(besta as int));
      assert(db == num_digits(bestb as int));
      if da > db {
          assert((best as int) == da);
      } else {
          assert((best as int) == db);
      }
      assert((best as int) == f(besta as int, bestb as int));
  }

  while i <= n
      invariant
          1 <= (i as int),
          (i as int) <= N + 1,
          1 <= (besta as int),
          1 <= (bestb as int),
          (besta as int) * (bestb as int) == N,
          (best as int) == f(besta as int, bestb as int),
          forall|a: int, b: int|
              1 <= a && a < (i as int) && is_factor_pair(a, b, N) ==> (best as int) <= f(a, b),
      decreases N - (i as int) + 1
  {
      if n % i == 0 {
          let b: i8 = n / i;
          let di = digits_i8(i);
          let db = digits_i8(b);
          let cand: i8 = if di > db { di } else { db };
          proof {
              let ia: int = i as int;
              let ba: int = b as int;
              assert(1 <= ia);
              assert(1 <= ba);
              // equality of candidate with spec f for this pair
              let dia: int = di as int; let dba: int = db as int;
              assert(dia == num_digits(ia));
              assert(dba == num_digits(ba));
              if di > db { assert((cand as int) == dia); } else { assert((cand as int) == dba); }
              assert((cand as int) == f(ia, ba));
          }
          if cand < best {
              best = cand;
              besta = i;
              bestb = b;
          } else {
              proof {
                  let ia: int = i as int;
                  let ba: int = b as int;
                  assert(1 <= ia);
                  assert(1 <= ba);
                  assert(is_factor_pair(ia, ba, N) ==> ia * ba == N);
                  let cand_int: int = cand as int;
                  assert(cand_int == f(ia, ba));
                  assert((best as int) <= f(ia, ba));
              }
          }
      }
      i = i + 1;
  }

  let result: i8 = best;

  proof {
      // existence of achieving pair
      assert(exists|a: int, b: int| is_factor_pair(a, b, N) && (result as int) == f(a, b)) by {
          assert(is_factor_pair(besta as int, bestb as int, N));
          assert((result as int) == f(besta as int, bestb as int));
      }
      // minimality over all factor pairs
      assert(forall|a: int, b: int| is_factor_pair(a, b, N) ==> (result as int) <= f(a, b)) by {
          if is_factor_pair(a, b, N) {
              assert(1 <= a && a <= N);
              assert(1 <= a && a < (i as int));
          }
      }
      // lower bound
      assert((result as int) >= 1);
  }

  result
}
// </vc-code>


}

fn main() {}