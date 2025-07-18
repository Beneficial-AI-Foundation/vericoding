use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

fn prime(p: u32) -> (ret: bool)
    ensures
        ret <==> spec_prime(p as int),
{
    if p <= 1 {
        return false;
    }
    
    let mut k = 2;
    /* code modified by LLM (iteration 4): added decreases clause to fix compilation error */
    while k < p
        invariant
            2 <= k <= p,
            forall|i: int| 2 <= i < k ==> #[trigger] (p as int % i) != 0,
        decreases p - k,
    {
        if p % k == 0 {
            return false;
        }
        k += 1;
    }
    true
}

fn checked_mul_thrice(x: u32, y: u32, z: u32) -> (ret: Option<u32>)
    ensures
        ret.is_some() ==> ret.unwrap() == x * y * z,
        ret.is_none() ==> x * y * z > u32::MAX,
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
    requires
        x > 1,
    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
{
    let mut a = 2;
    /* code modified by LLM (iteration 4): added decreases clause to fix compilation error */
    while a * a * a <= x
        invariant
            a >= 2,
            forall|i: int, j: int, k: int| 2 <= i < a && 2 <= j && 2 <= k &&
                spec_prime(i) && spec_prime(j) && spec_prime(k) ==> i * j * k != x,
        decreases x - a * a * a,
    {
        if prime(a) {
            let mut b = 2;
            /* code modified by LLM (iteration 4): added decreases clause to fix compilation error */
            while b * b <= x / a
                invariant
                    b >= 2,
                    spec_prime(a as int),
                    forall|j: int, k: int| 2 <= j < b && 2 <= k &&
                        spec_prime(j) && spec_prime(k) ==> (a as int) * j * k != x,
                decreases x / a - b * b,
            {
                if prime(b) && x % (a * b) == 0 {
                    let c = x / (a * b);
                    if c >= 2 && prime(c) {
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