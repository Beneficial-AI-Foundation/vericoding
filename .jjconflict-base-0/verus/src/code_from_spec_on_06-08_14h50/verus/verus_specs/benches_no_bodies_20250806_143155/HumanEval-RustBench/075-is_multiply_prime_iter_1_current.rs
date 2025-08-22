use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

fn prime(p: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> spec_prime(p as int),
    // post-conditions-end
{
    if p <= 1 {
        return false;
    }
    
    let mut i = 2;
    while i < p
        invariant
            2 <= i <= p,
            forall|k: int| 2 <= k < i ==> (p as int) % k != 0,
    {
        if p % i == 0 {
            return false;
        }
        i += 1;
    }
    true
}

fn checked_mul_thrice(x: u32, y: u32, z: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        ret.is_some() ==> ret.unwrap() == x * y * z,
        ret.is_none() ==> x * y * z > u32::MAX,
    // post-conditions-end
{
    let temp = x.checked_mul(y);
    if temp.is_none() {
        return None;
    }
    let temp_val = temp.unwrap();
    let result = temp_val.checked_mul(z);
    if result.is_none() {
        return None;
    }
    Some(result.unwrap())
}

fn is_multiply_prime(x: u32) -> (ans: bool)
    // pre-conditions-start
    requires
        x > 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
    // post-conditions-end
{
    let mut a = 2;
    while a <= x
        invariant
            2 <= a <= x + 1,
            forall|i: int, j: int, k: int| 
                2 <= i < a && spec_prime(i) && spec_prime(j) && spec_prime(k) 
                ==> x != i * j * k,
    {
        if prime(a) {
            let mut b = 2;
            while b <= x / a
                invariant
                    2 <= b <= x / a + 1,
                    spec_prime(a as int),
                    forall|j: int, k: int| 
                        2 <= j < b && spec_prime(j) && spec_prime(k) 
                        ==> x != (a as int) * j * k,
            {
                if prime(b) && x % a == 0 && (x / a) % b == 0 {
                    let c = x / a / b;
                    if c >= 2 && prime(c) && a * b * c == x {
                        return true;
                    }
                }
                b += 1;
            }
        }
        a += 1;
    }
    false
}

}
fn main() {}