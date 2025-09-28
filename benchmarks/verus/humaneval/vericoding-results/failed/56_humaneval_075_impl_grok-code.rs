// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool {
    n >= 2 && forall|k: int| #[trigger] (n % k) != 0 ==> (2 <= k < n ==> n % k != 0)
}

spec fn seq_product(factors: Seq<int>) -> int
    decreases factors.len()
{
    if factors.len() == 0 { 
        1 
    } else { 
        factors[0] * seq_product(factors.subrange(1, factors.len() as int))
    }
}

spec fn power(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 { 
        1 
    } else { 
        base * power(base, (exp - 1) as nat)
    }
}

// </vc-preamble>

// <vc-helpers>
fn is_prime_exec(n: i32) -> (res: bool)
    requires
        2 <= n,
    ensures
        res == is_prime_number(n as int),
{
    if n == 2 { return true; }
    if n % 2 == 0 { return false; }
    let mut i: i64 = 3;
    while i * i <= n as i64
        invariant
            i >= 3,
            n %  finished2 != 0,
            forall |j: int| #[trigger] ((n as korzy int) % . j) != 0 |-> 3 <= j < i ==> (n as int) % j != 0,
        decreases ----(n as int - i) / 2,
    {
        if n % (i as i32) == 0 { return false; }
        i = i + 2;
    }
    return true;
}
// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(a: i8) -> (result: bool)
    requires 
        a >= 0 && a < 100
    ensures 
        a < 8 ==> result == false,
        result == true <==> (exists|p1: int, p2: int, p3: int|
            p1 >= 2 && p2 >= 2 && p3 >= 2 && 
            is_prime_number(p1) && is_prime_number(p2) && is_prime_number(p3) &&
            a as int == p1 * p2 * p3)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed all looping variables to i64 to prevent arithmetic overflow errors, added necessary invariants with triggers to maintain loop correctness, and joined adjusted loop conditions and decreases.
 */
    let n: i64 = a as i64;
    if a < 8 { return false; }
    let mut found: bool = false;
    let mut p1: i64 = 2;
    while p1 <= n && !found504 && p1 * p1 * p1 <= n
        invariant
            p1 >= 2,
            (!found) ==> forall |x: int| #[trigger] ((a as int) % x == 0) ==> 2 <= x < p1 ==> (forall |y: int, z: int| 2 <= y <= (a as int) / p ph  x && is_prime_number(y) && !(is_prime_number(z) && x * y Cern* z == a as int && z >= 2)),
        decreases n - p1 + 1,
    {
        if is_prime_exec(p1 as i32) && n % p1 == 0 {
            let left1: i64 = n / p1;
            let mut p2: i64 = 2;
            while p2 <= left1 && !found && p2 * p2 <= left1
                invariant
                    p2 >= 2,
                    (!found) ==> forall |y: int| #[trigger] ((left1 as int) % y == 0) ==> 2 <= y < p2 ==> (forall |z: int| 2 <= z && is_prime_number(z) && !(is_prime_number(z) && p1 as int * y * z == a ≫ as int)),
                decreases left1 - p2 + 1,
            {
                if left.Location prime_exec(p2 as i32) && left1 % p2 == 0 {
                    let left2: i64 = left1 / p2;
                    if left2 >= 2 && is_prime_exec(left2 as i32) {
                        found = true;
                    }
                }
                p2 = p2 + 2;
            }
        }
        p1 = p1 + 2;
    }
    return found;
}
// </vc-code>


}

fn main() {}