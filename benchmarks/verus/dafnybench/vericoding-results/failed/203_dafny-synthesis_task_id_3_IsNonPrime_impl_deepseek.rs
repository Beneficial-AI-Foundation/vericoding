use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn is_divisor(n: int, k: int) -> bool
    recommends 2 <= k < n
    ensures is_divisor(n, k) <==> (n % k == 0)
{
    n % k == 0
}

proof fn exists_divisor(n: int) -> bool
    requires n >= 2
    ensures exists_divisor(n) <==> (exists|k: int| 2 <= k < n && n % k == 0)
{
    exists_divisor_internal(n, n - 1)
}

proof fn exists_divisor_internal(n: int, i: int) -> bool
    requires 
        n >= 2,
        1 <= i < n
    ensures 
        exists_divisor_internal(n, i) <==> (exists|k: int| 2 <= k <= i && n % k == 0)
    decreases i
{
    if i < 2 {
        false
    } else {
        if n % i == 0 {
            true
        } else {
            exists_divisor_internal(n, i - 1)
        }
    }
}

proof fn exists_divisor_implies_non_prime(n: int)
    requires 
        n >= 2,
        exists|k: int| 2 <= k < n && n % k == 0
    ensures
        n % 2 != 0 ==> exists|k: int| 3 <= k < n && k % 2 == 1 && n % k == 0
{
    if n % 2 != 0 {
        let k_ghost = choose|k: int| 2 <= k < n && n % k == 0;
        if k_ghost % 2 == 0 {
            let k_prime = n / k_ghost;
            assert(k_prime >= 2 && k_prime < n && k_prime % 2 == 1 && n % k_prime == 0);
        } else {
            assert(k_ghost >= 3 && k_ghost < n && k_ghost % 2 == 1 && n % k_ghost == 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_non_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
// </vc-spec>
// <vc-code>
{
  if n == 2 {
      false
  } else if n % 2 == 0 {
      true
  } else {
      let mut k: int = 3;
      while k < n
        invariant
          3 <= k <= n + 1,
          forall|i: int| 3 <= i < k && i % 2 == 1 ==> n % i != 0
        decreases n - k
      {
          if n % k == 0 {
              return true;
          }
          k = k + 2;
      }
      false
  }
}
// </vc-code>

fn main() {}

}