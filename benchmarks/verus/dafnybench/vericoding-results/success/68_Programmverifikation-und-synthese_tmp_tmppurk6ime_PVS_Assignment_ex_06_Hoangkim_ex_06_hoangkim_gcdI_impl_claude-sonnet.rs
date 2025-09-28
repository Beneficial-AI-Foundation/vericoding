use vstd::prelude::*;

verus! {

//Problem01
//a)
spec fn gcd(x: int, y: int) -> int
    recommends x > 0 && y > 0
    decreases x + y when x > 0 && y > 0
{
    if x == y { x }
    else if x > y { gcd(x - y, y) }
    else { gcd(x, y - x) }
}

//b)
spec fn gcd_prime(x: int, y: int) -> int
    recommends x > 0 && y > 0
    decreases if x > y { x } else { y }, x + y when x > 0 && y > 0
{
    if x == y { x }
    else if x > y { gcd_prime(x - y, y) }
    else { gcd(y, x) }
}

// <vc-helpers>
proof fn gcd_decreases_lemma(x: int, y: int)
    requires x > 0 && y > 0 && x != y
    ensures (if x > y { (x - y) + y } else { x + (y - x) }) < x + y
{
    if x > y {
        assert((x - y) + y == x);
        assert(x < x + y);
    } else {
        assert(x + (y - x) == y);
        assert(y < x + y);
    }
}

proof fn gcd_invariant_lemma(x: int, y: int, orig_x: int, orig_y: int)
    requires x > 0 && y > 0 && orig_x > 0 && orig_y > 0
    ensures gcd(x, y) == gcd(orig_x, orig_y) ==> 
            (x != y ==> (x > y ==> gcd(x - y, y) == gcd(orig_x, orig_y)) &&
                        (x <= y ==> gcd(x, y - x) == gcd(orig_x, orig_y)))
{
}
// </vc-helpers>

// <vc-spec>
fn gcd_i(m: int, n: int) -> (d: int)
    requires m > 0 && n > 0
    ensures d == gcd(m, n)
// </vc-spec>
// <vc-code>
{
    let mut x = m;
    let mut y = n;
    
    while x != y
        invariant 
            x > 0 && y > 0,
            gcd(x, y) == gcd(m, n),
        decreases x + y
    {
        proof {
            gcd_decreases_lemma(x, y);
        }
        
        if x > y {
            x = x - y;
        } else {
            y = y - x;
        }
    }
    
    x
}
// </vc-code>

fn main() {
}

}