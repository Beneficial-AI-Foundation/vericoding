// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): integer sqrt and square comparison lemma */
fn integer_sqrt(n: u64) -> (s: u64)
    ensures
        (s as u128) * (s as u128) <= (n as u128),
        ((s + 1u64) as u128) * ((s + 1u64) as u128) > (n as u128)
{
    let mut lo: u128 = 0;
    let mut hi: u128 = (n as u128) + (1u128);
    while lo + 1 < hi
        invariant
            lo <= hi,
            hi <= (n as u128) + (1u128),
        decreases hi - lo
    {
        let mid = (lo + hi) / 2;
        if mid * mid <= (n as u128) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let s = lo as u64;
    s
}

proof fn le_from_sq_le(a: u128, b: u128)
    requires a * a <= b * b
    ensures a <= b
{
    proof {
        if a <= b { return; }
        assert(a > b);
        assert(a >= b + 1);
        assert(a * a >= (b + 1) * (b + 1));
        assert((b + 1) * (b + 1) > b * b);
        assert(a * a > b * b);
        assert(false);
    }
}

// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute sqrt and prove equivalence avoiding lt_from_sq_lt */
  let s = integer_sqrt(n);
  let result = ((s as u128) * (s as u128) == (n as u128));
  proof {
    if result {
      assert((s as u128) * (s as u128) == (n as u128));
      assert((s as nat) * (s as nat) == n as nat);
      assert(exists |i: nat| (i * i) == n as nat);
    }
    else {
      if exists |i: nat| (i * i) == n as nat {
        let i = choose |i: nat| (i * i) == n as nat;
        let iu = i as u128;
        // i^2 == n
        assert(iu * iu == n as u128);
        // bounds from integer_sqrt
        assert((s as u128) * (s as u128) <= n as u128);
        assert(((s + 1u64) as u128) * ((s + 1u64) as u128) > n as u128);
        // derive s <= iu
        le_from_sq_le(s as u128, iu);
        assert(s as u128 <= iu);
        // show iu < s+1 by contradiction: if iu >= s+1 then iu*iu >= (s+1)^2 > n = iu*iu
        if iu >= (s as u128) + (1u128) {
            assert(iu * iu >= ((s as u128) + (1u128)) * ((s as u128) + (1u128)));
            assert(((s + 1u64) as u128) * ((s + 1u64) as u128) > n as u128);
            assert(iu * iu > n as u128);
            assert(false);
        }
        assert(iu < (s as u128) + (1u128));
        assert(iu <= s as u128);
        assert(iu == s as u128);
        assert((s as u128) * (s as u128) == n as u128);
      }
    }
  }
  result
}

// </vc-code>

}
fn main() {}