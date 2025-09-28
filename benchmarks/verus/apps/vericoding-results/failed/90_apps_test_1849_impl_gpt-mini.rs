// <vc-preamble>
use vstd::prelude::*;

verus! {

spec const MOD: int = 998244353int;

spec fn valid_input(n: int) -> bool
{
  n >= 1
}

spec fn pow(base: int, exp: int, modulus: int) -> int
  decreases exp
{
  if exp <= 0 { 1int }
  else { (base * pow(base, exp - 1, modulus)) % modulus }
}

spec fn block_count_formula(n: int, i: int) -> int
  recommends n >= 1 && 1 <= i <= n
{
  if i == n { 10int }
  else { 
    ((2int * 9int * pow(10int, n - i - 1, MOD) * 10int) + 
     (if i < n - 1 { ((n - 1 - i) * 9int * 9int * pow(10int, n - i - 2, MOD) * 10int) } else { 0int })) % MOD
  }
}

spec fn valid_result(result: Seq<int>, n: int) -> bool
  recommends n >= 1
{
  result.len() == n &&
  (forall|k: int| 0 <= k < n ==> #[trigger] result[k] >= 0 && #[trigger] result[k] < MOD) &&
  (n >= 1 ==> result[n-1] == 10int) &&
  (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i] == block_count_formula(n, i+1))
}
// </vc-preamble>

// <vc-helpers>
spec fn pow_mod(base: int, exp: int, modulus: int) -> int
  requires
      exp >= 0,
  ensures
      result == pow(base, exp, modulus),
  decreases exp
{
    if exp == 0 { 1int } else { (base * pow_mod(base, exp - 1, modulus)) % modulus }
}

spec fn block_count_calc(n: int, i: int) -> int
  requires
      n >= 1, 1 <= i <= n,
  ensures
      result == block_count_formula(n, i),
{
    if i == n { 10int }
    else {
        let p1 = pow_mod(10int, n - i - 1, MOD);
        let extra = if i < n - 1 { ((n - 1 - i) * 9int * 9int * pow_mod(10int, n - i - 2, MOD) * 10int) } else { 0int };
        ((2int * 9int * p1 * 10int) + extra) % MOD
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
  requires valid_input(n as int)
  ensures valid_result(result@.map(|_index: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
{
    let nn: int = n as int;
    let mut out: Vec<i8> = Vec::new();
    let mut i: int = 1int;
    while i <= nn
        invariant
            1 <= i,
            i <= nn + 1int,
            out.len() as int == i - 1int,
        decreases nn - (i - 1int)
    {
        let mut val: int = 0int;
        if i == nn {
            val = 10int;
        } else {
            let mut p1: int = 1int;
            let mut e1: int = nn - i - 1int;
            while e1 > 0
                invariant
                    e1 >= 0,
                    p1 >= 0,
                decreases e1
            {
                p1 = (p1 * 10int) % MOD;
                e1 -= 1int;
            }
            let mut extra: int = 0int;
            if i < nn - 1int {
                let mut p2: int = 1int;
                let mut e2: int = nn - i - 2int;
                while e2 > 0
                    invariant
                        e2 >= 0,
                        p2 >= 0,
                    decreases e2
                {
                    p2 = (p2 * 10int) % MOD;
                    e2 -= 1int;
                }
                extra = ((nn - 1int - i) * 9int * 9int * p2 * 10int) % MOD;
            }
            val = ((2int * 9int * p1 * 10int) + extra) % MOD;
        }
        out.push(val as i8);
        i += 1int;
    }
    out
}
// </vc-code>


}

fn main() {}