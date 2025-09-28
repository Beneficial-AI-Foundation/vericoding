// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow(base: int, exp: int) -> int
  decreases exp
{
  if exp <= 0 { 1 }
  else { base * pow(base, exp - 1) }
}
// </vc-preamble>

// <vc-helpers>
fn pow_add(base: int, m: int, n: int)
    requires
        m >= 0,
        n >= 0,
    ensures
        pow(base, m + n) == pow(base, m) * pow(base, n),
    decreases n
{
    if n == 0 {
        proof {
            assert(pow(base, m + 0) == pow(base, m));
            assert(pow(base, 0) == 1);
            assert(pow(base, m) * pow(base, 0) == pow(base, m));
            assert(pow(base, m + 0) == pow(base, m) * pow(base, 0));
        }
    } else {
        pow_add(base, m, n - 1);
        proof {
            assert(pow(base, m + n) == base * pow(base, m + n - 1));
            assert(pow(base, m + n - 1) == pow(base, m) * pow(base, n - 1));
            assert(base * (pow(base, m) * pow(base, n - 1)) == pow(base, m) * (base * pow(base, n - 1)));
            assert(base * pow(base, n - 1) == pow(base, n));
            assert(pow(base, m + n) == pow(base, m) * pow(base, n));
        }
    }
}

fn pow3_10()
    ensures
        pow(3, 10) == 59049,
    decreases 10
{
    proof {
        assert(pow(3, 0) == 1);
        assert(pow(3, 1) == 3 * pow(3, 0));
        assert(pow(3, 1) == 3);
        assert(pow(3, 2) == 3 * pow(3, 1));
        assert(pow(3, 2) == 9);
        assert(pow(3, 3) == 3 * pow(3, 2));
        assert(pow(3, 3) == 27);
        assert(pow(3, 4) == 3 * pow(3, 3));
        assert(pow(3, 4) == 81);
        assert(pow(3, 5) == 3 * pow(3, 4));
        assert(pow(3, 5) == 243);
        assert(pow(3, 6) == 3 * pow(3, 5));
        assert(pow(3, 6) == 729);
        assert(pow(3, 7) == 3 * pow(3, 6));
        assert(pow(3, 7) == 2187);
        assert(pow(3, 8) == 3 * pow(3, 7));
        assert(pow(3, 8) == 6561);
        assert(pow(3, 9) == 3 * pow(3, 8));
        assert(pow(3, 9) == 19683);
        assert(pow(3, 10) == 3 * pow(3, 9));
        assert(pow(3, 10) == 59049);
    }
}

fn pow2_10()
    ensures
        pow(2, 10) == 1024,
    decreases 10
{
    proof {
        assert(pow(2, 0) == 1);
        assert(pow(2, 1) == 2 * pow(2, 0));
        assert(pow(2, 1) == 2);
        assert(pow(2, 2) == 2 * pow(2, 1));
        assert(pow(2, 2) == 4);
        assert(pow(2, 3) == 2 * pow(2, 2));
        assert(pow(2, 3) == 8);
        assert(pow(2, 4) == 2 * pow(2, 3));
        assert(pow(2, 4) == 16);
        assert(pow(2, 5) == 2 * pow(2, 4));
        assert(pow(2, 5) == 32);
        assert(pow(2, 6) == 2 * pow(2, 5));
        assert(pow(2, 6) == 64);
        assert(pow(2, 7) == 2 * pow(2, 6));
        assert(pow(2, 7) == 128);
        assert(pow(2, 8) == 2 * pow(2, 7));
        assert(pow(2, 8) == 256);
        assert(pow(2, 9) == 2 * pow(2, 8));
        assert(pow(2, 9) == 512);
        assert(pow(2, 10) == 2 * pow(2, 9));
        assert(pow(2, 10) == 1024);
    }
}

fn pow_3_20_gt_10_2_20()
    ensures
        pow(3, 20) > 10 * pow(2, 20),
    decreases 0
{
    proof {
        pow3_10();
        pow2_10();
        pow_add(3, 10, 10);
        pow_add(2, 10, 10);
        assert(pow(3, 20) == pow(3, 10) * pow(3, 10));
        assert(pow(2, 20) == pow(2, 10) * pow(2, 10));
        assert(pow(3, 10) == 59049);
        assert(pow(2, 10) == 1024);
        assert(pow(3, 10) * pow(3, 10) == 3486784401);
        assert(pow(2, 10) * pow(2, 10) == 1048576);
        assert(3486784401 > 10 * 1048576);
        assert(pow(3, 20) > 10 * pow(2, 20));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (years: i8)
  requires 
      1 <= a <= b <= 10,
      forall|base: int, exp: int| exp >= 0 ==> (
          (exp == 0 ==> pow(base, exp) == 1) &&
          (exp > 0 && base > 0 ==> pow(base, exp) > 0) &&
          (exp > 0 && base == 0 ==> pow(base, exp) == 0)
      ),
  ensures 
      years >= 0,
      (a as int) * pow(3, years as int) > (b as int) * pow(2, years as int),
      years == 0 || (a as int) * pow(3, (years - 1) as int) <= (b as int) * pow(2, (years - 1) as int),
// </vc-spec>
// <vc-code>
{
    let mut y: int = 0;
    while (a as int) * pow(3, y) <= (b as int) * pow(2, y)
        invariant
            0 <= y <= 20,
            forall|k: int| 0 <= k < y ==> (a as int) * pow(3, k) <= (b as int) * pow(2, k),
        decreases 21 - y
    {
        proof {
            // the loop cannot hold when y == 20 because pow(3,20) > 10 * pow(2,20)
            if y == 20 {
                pow_3_20_gt_10_2_20();
                assert((a as int) >= 1);
                assert((b as int) <= 10);
                assert((a as int) * pow(3, 20) > (b as int) * pow(2, 20));
                // contradiction with the loop condition
                assert(false);
            }
        }
        y = y + 1;
    }
    let years: i8 = y as i8;
    years
}
// </vc-code>


}

fn main() {}