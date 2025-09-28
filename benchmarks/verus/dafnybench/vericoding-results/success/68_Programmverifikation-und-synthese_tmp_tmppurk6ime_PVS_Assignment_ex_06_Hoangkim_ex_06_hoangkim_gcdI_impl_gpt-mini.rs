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
proof fn gcd_sub_left(x: int, y: int)
    requires x > y && y > 0
    ensures gcd(x - y, y) == gcd(x, y)
    decreases x + y
{
    if x == y {
        // impossible
    } else if x > y {
        // By definition of gcd, when x > y the recursive branch returns gcd(x - y, y)
        assert(gcd(x, y) == gcd(x - y, y));
    } else {
        // impossible
    }
}

proof fn gcd_sub_right(x: int, y: int)
    requires y > x && x > 0
    ensures gcd(x, y - x) == gcd(x, y)
    decreases x + y
{
    if x == y {
        // impossible
    } else if x > y {
        // impossible
    } else {
        // By definition of gcd, when y > x the recursive branch returns gcd(x, y - x)
        assert(gcd(x, y) == gcd(x, y - x));
    }
}
// </vc-helpers>

// <vc-spec>
fn gcd_i(m: int, n: int) -> (d: int)
    requires m > 0 && n > 0
    ensures d == gcd(m, n)
// </vc-spec>
// <vc-code>
{
    let mut a = m;
    let mut b = n;
    while a != b
        invariant a > 0 && b > 0 && gcd(a, b) == gcd(m, n)
        decreases a + b
    {
        if a > b {
            let oa = a;
            let ob = b;
            a = oa - ob;
            proof {
                assert(oa > ob);
                assert(ob > 0);
                assert(gcd(oa, ob) == gcd(m, n));
                gcd_sub_left(oa, ob);
                // after lemma: gcd(oa - ob, ob) == gcd(oa, ob)
                assert(gcd(a, b) == gcd(m, n));
                assert(a > 0);
                assert(b > 0);
            }
        } else {
            let oa = a;
            let ob = b;
            b = ob - oa;
            proof {
                assert(ob > oa);
                assert(oa > 0);
                assert(gcd(oa, ob) == gcd(m, n));
                gcd_sub_right(oa, ob);
                // after lemma: gcd(oa, ob - oa) == gcd(oa, ob)
                assert(gcd(a, b) == gcd(m, n));
                assert(a > 0);
                assert(b > 0);
            }
        }
    }
    a
}
// </vc-code>

fn main() {
}

}