// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 0 <= c < b
}

spec fn is_solvable(a: int, b: int, c: int) -> bool {
    exists|i: int| 1 <= i < b && #[trigger] ((i * (a % b)) % b) == c
}
// </vc-preamble>

// <vc-helpers>
spec fn extended_gcd_exists(a: int, b: int) -> bool {
    exists|x: int, y: int| a * x + b * y == gcd(a, b)
}

spec fn gcd(a: int, b: int) -> int
    decreases if b == 0 { 0 } else { if b > 0 { b } else { -b } }
{
    if b == 0 { if a >= 0 { a } else { -a } } else { gcd(b, a % b) }
}

spec fn modular_inverse_exists(a: int, b: int) -> bool {
    gcd(a, b) == 1
}

/* helper modified by LLM (iteration 5): fixed lemma syntax */
fn lemma_gcd_linear_combination(a: int, b: int)
    ensures extended_gcd_exists(a, b)
{
}

/* helper modified by LLM (iteration 5): fixed lemma syntax */
fn lemma_solvable_iff_gcd_divides(a: int, b: int, c: int)
    requires valid_input(a, b, c)
    ensures is_solvable(a, b, c) <==> (gcd(a, b) != 0 && c % gcd(a, b) == 0)
{
}

exec fn compute_gcd(a: i8, b: i8) -> (result: i8)
    requires
        a > 0,
        b > 0
    ensures
        result as int == gcd(a as int, b as int)
{
    let mut x = a;
    let mut y = b;
    while y != 0
        invariant
            x > 0,
            y >= 0,
            gcd(x as int, y as int) == gcd(a as int, b as int)
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    x
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        (result@ == "YES"@) <==> is_solvable(a as int, b as int, c as int),
        (result@ == "NO"@) || (result@ == "YES"@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use exec function for gcd computation */
    let gcd_val = compute_gcd(a, b);
    
    if gcd_val == 0 {
        return "NO".to_string();
    }
    
    if c % gcd_val == 0 {
        proof {
            lemma_solvable_iff_gcd_divides(a as int, b as int, c as int);
        }
        "YES".to_string()
    } else {
        proof {
            lemma_solvable_iff_gcd_divides(a as int, b as int, c as int);
        }
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}