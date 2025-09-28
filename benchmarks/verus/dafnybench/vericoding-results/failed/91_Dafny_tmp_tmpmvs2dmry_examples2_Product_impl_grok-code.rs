use vstd::prelude::*;

verus! {

spec fn gcd(m: nat, n: nat) -> nat
recommends m > 0 && n > 0
decreases m + n
{
    if m == n { 
        n 
    } else if m > n { 
        gcd(sub(m, n), n)
    } else {
        gcd(m, sub(n, m))
    }
}

spec fn exp(x: real, n: nat) -> real
decreases n
{
    if n == 0 {
        1.0
    } else if x == 0.0 {
        0.0
    } else if n == 0 && x == 0.0 {
        1.0
    } else {
        x * exp(x, sub(n, 1))
    }
}

// <vc-helpers>
spec fn mul_left(a: int, b: int) -> int {
  a * b
}

spec fn mul_right(a: int, b: int) -> int {
  b * a
}

proof fn mul_comm(m: int, n: int) {
  assert(m * n == n * m);
}

spec fn product_spec(m: int, n: nat) -> int
  requires m >= 0 && (n == 0 || m as int * n as int <= u64::MAX as int)
  decreases n
  ensures product_spec(m, n) == m * n
{
  if n == 0 {
    0
  } else {
    m + product_spec(m, n - 1)
  }
}

proof fn product_spec_sufficient(m: int, n: nat) 
  ensures product_spec(m, n) == m * n
{
  decreases n;
  assert(m >= 0);
  assert(n == 0 || m as int * n as int <= u64::MAX as int);
  if n == 0 {
    assert(product_spec(m, 0) == 0);
    assert(m * 0 == 0);
  } else {
    product_spec_sufficient(m, n - 1);
    assert(product_spec(m, n) == m + product_spec(m, n-1));
    assert(product_spec(m, n-1) == m * (n-1));
    assert(m + product_spec(m, n-1) == m + m * (n-1));
    assert(m + m * (n-1) == m * (1 as int + (n-1) as int));
    assert(1 as int + (n-1) as int == n as int);
    assert(m * n as int == product_spec(m, n));
  }
}
// </vc-helpers>

// <vc-spec>
fn Product(m: u64, n: u64) -> (res: u64)
ensures res == m * n
// </vc-spec>
// <vc-code>
{
  let m_int = m as int;
  let n_nat = n as nat;
  if n == 0 {
    0
  } else {
    assert(m_int >= 0);
    assert(n_nat == 0 || m_int * n_nat as int <= u64::MAX as int);
    assert(product_spec(m_int, n_nat) >= 0);
    assert(product_spec(m_int, n_nat) <= u64::MAX as int);
    proof { product_spec_sufficient(m_int, n_nat); }
    (product_spec(m_int, n_nat) as u64)
  }
}
// </vc-code>

fn main() {}

}