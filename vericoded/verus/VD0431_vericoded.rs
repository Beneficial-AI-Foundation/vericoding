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
proof fn lemma_gcd_reduction_left(x: int, y: int)
    requires
        x > 0 && y > 0,
        x > y,
    ensures
        gcd(x, y) == gcd(x - y, y)
{
    assert(x != y);
    reveal_with_fuel(gcd, 1);
    assert(gcd(x, y) == gcd(x - y, y));
}

proof fn lemma_gcd_reduction_right(x: int, y: int)
    requires
        x > 0 && y > 0,
        y > x,
    ensures
        gcd(x, y) == gcd(x, y - x)
{
    assert(x != y);
    reveal_with_fuel(gcd, 1);
    assert(gcd(x, y) == gcd(x, y - x));
}

proof fn lemma_gcd_equal_case(x: int)
    requires
        x > 0,
    ensures
        gcd(x, x) == x
{
    reveal_with_fuel(gcd, 1);
    assert(gcd(x, x) == x);
}
// </vc-helpers>

// <vc-spec>
fn gcd_i(m: int, n: int) -> (d: int)
    requires m > 0 && n > 0
    ensures d == gcd(m, n)
// </vc-spec>
// <vc-code>
{
    let ghost g = gcd(m, n);

    let mut a = m;
    let mut b = n;

    while a != b
        invariant a > 0 && b > 0 && gcd(a, b) == g
        decreases a + b
    {
        if a > b {
            let old_a = a;
            let old_b = b;
            proof {
                assert(gcd(old_a, old_b) == g);
                lemma_gcd_reduction_left(old_a, old_b);
            }
            a = old_a - old_b;
            proof {
                assert(old_a > old_b);
                assert(old_a - old_b > 0);
                assert(a == old_a - old_b);
                assert(b == old_b);
                assert(gcd(a, b) == gcd(old_a - old_b, old_b));
                assert(gcd(old_a - old_b, old_b) == gcd(old_a, old_b));
                assert(gcd(a, b) == g);
                // decreases
                assert(a + b == (old_a - old_b) + old_b);
                assert(a + b == old_a);
                assert(old_b > 0);
                assert(old_a < old_a + old_b);
                assert(a + b < old_a + old_b);
            }
        } else {
            assert(a < b);
            let old_a = a;
            let old_b = b;
            proof {
                assert(gcd(old_a, old_b) == g);
                assert(old_b > old_a);
                lemma_gcd_reduction_right(old_a, old_b);
            }
            b = old_b - old_a;
            proof {
                assert(old_b > old_a);
                assert(old_b - old_a > 0);
                assert(b == old_b - old_a);
                assert(a == old_a);
                assert(gcd(a, b) == gcd(old_a, old_b - old_a));
                assert(gcd(old_a, old_b - old_a) == gcd(old_a, old_b));
                assert(gcd(a, b) == g);
                // decreases
                assert(a + b == old_a + (old_b - old_a));
                assert(a + b == old_b);
                assert(old_a > 0);
                assert(old_b < old_a + old_b);
                assert(a + b < old_a + old_b);
            }
        }
    }

    assert(a == b);
    proof {
        lemma_gcd_equal_case(a);
        assert(gcd(a, b) == gcd(a, a));
        assert(gcd(a, a) == a);
        assert(gcd(a, b) == g);
        assert(a == g);
    }

    a
}
// </vc-code>

fn main() {
}

}