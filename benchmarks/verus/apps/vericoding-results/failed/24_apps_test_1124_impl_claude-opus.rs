// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(values: Seq<int>) -> bool {
    values.len() >= 1 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
}

spec fn gcd(a: int, b: int) -> int
    decreases (if a >= b { a } else { b }) when a > 0 && b > 0
{
    if a > 0 && b > 0 {
        if a == b {
            a
        } else if a > b {
            gcd(a - b, b)
        } else {
            gcd(a, b - a)
        }
    } else {
        1
    }
}

spec fn gcd_seq(values: Seq<int>, index: int, current: int) -> int
    decreases values.len() - index when 0 <= index <= values.len() && current > 0 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0
{
    if 0 <= index <= values.len() && current > 0 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0 {
        if index == values.len() {
            current
        } else {
            gcd_seq(values, index + 1, gcd(current, values[index as int]))
        }
    } else {
        1
    }
}

spec fn gcd_of_all(values: Seq<int>) -> int {
    if values.len() >= 1 && forall|i: int| 0 <= i < values.len() ==> values[i] > 0 {
        gcd_seq(values, 1, values[0])
    } else {
        1
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn values_as_int(values: Seq<i8>) -> Seq<int> {
    values.map(|i, x| x as int)
}

fn gcd_exec(a: i8, b: i8) -> (result: i8)
    requires
        a > 0,
        b > 0,
    ensures
        result > 0,
        result as int == gcd(a as int, b as int),
{
    let mut x = a;
    let mut y = b;
    while x != y
        invariant
            x > 0,
            y > 0,
            gcd(x as int, y as int) == gcd(a as int, b as int),
        decreases (if x >= y { x } else { y }) as int,
    {
        if x > y {
            x = x - y;
        } else {
            y = y - x;
        }
    }
    x
}

/* helper modified by LLM (iteration 4): Added proof for gcd positivity */
proof fn gcd_positive(a: int, b: int)
    requires
        a > 0,
        b > 0,
    ensures
        gcd(a, b) > 0,
    decreases (if a >= b { a } else { b }),
{
    if a == b {
        assert(gcd(a, b) == a);
    } else if a > b {
        gcd_positive(a - b, b);
    } else {
        gcd_positive(a, b - a);
    }
}

/* helper modified by LLM (iteration 4): Fixed postcondition proofs */
proof fn gcd_divides_both(a: int, b: int)
    requires
        a > 0,
        b > 0,
    ensures
        a % gcd(a, b) == 0,
        b % gcd(a, b) == 0,
    decreases (if a >= b { a } else { b }),
{
    if a == b {
        assert(gcd(a, b) == a);
        assert(a % a == 0);
        assert(b % a == 0);
    } else if a > b {
        gcd_divides_both(a - b, b);
        let g = gcd(a - b, b);
        assert(gcd(a, b) == g);
        assert((a - b) % g == 0);
        assert(b % g == 0);
        assert(a % g == 0);
    } else {
        gcd_divides_both(a, b - a);
        let g = gcd(a, b - a);
        assert(gcd(a, b) == g);
        assert(a % g == 0);
        assert((b - a) % g == 0);
        assert(b % g == 0);
    }
}

/* helper modified by LLM (iteration 4): Fixed next_gcd positivity proof */
proof fn gcd_seq_divides_all(values: Seq<int>, index: int, current: int, k: int)
    requires
        0 <= index <= values.len(),
        current > 0,
        forall|i: int| 0 <= i < values.len() ==> values[i] > 0,
        0 <= k < index,
        values[k] % current == 0,
    ensures
        values[k] % gcd_seq(values, index, current) == 0,
    decreases values.len() - index,
{
    if index == values.len() {
        assert(gcd_seq(values, index, current) == current);
    } else {
        let next_gcd = gcd(current, values[index as int]);
        gcd_positive(current, values[index as int]);
        assert(next_gcd > 0);
        gcd_divides_both(current, values[index as int]);
        assert(current % next_gcd == 0);
        assert(values[k] % current == 0);
        let q1 = values[k] / current;
        let q2 = current / next_gcd;
        assert(values[k] == q1 * current);
        assert(current == q2 * next_gcd);
        assert(values[k] == q1 * q2 * next_gcd);
        assert(values[k] % next_gcd == 0);
        gcd_seq_divides_all(values, index + 1, next_gcd, k);
    }
}

/* helper modified by LLM (iteration 4): Fixed next_gcd positivity and logic */
proof fn gcd_seq_divides_remaining(values: Seq<int>, index: int, current: int, k: int)
    requires
        0 <= index <= values.len(),
        current > 0,
        forall|i: int| 0 <= i < values.len() ==> values[i] > 0,
        index <= k < values.len(),
    ensures
        values[k] % gcd_seq(values, index, current) == 0,
    decreases values.len() - index,
{
    if index == values.len() {
        assert(false);
    } else {
        let next_gcd = gcd(current, values[index as int]);
        gcd_positive(current, values[index as int]);
        assert(next_gcd > 0);
        if k == index {
            gcd_divides_both(current, values[index as int]);
            assert(values[index as int] % next_gcd == 0);
            assert(values[k] % next_gcd == 0);
            gcd_seq_divides_all(values, index + 1, next_gcd, k);
        } else {
            gcd_seq_divides_remaining(values, index + 1, next_gcd, k);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(values: Vec<i8>) -> (result: i8)
    requires valid_input(values_as_int(values@)) && values.len() <= 127
    ensures 
        result > 0 &&
        result as int == gcd_of_all(values_as_int(values@)) &&
        forall|i: int| 0 <= i < values@.len() ==> (values@[i] as int) % (result as int) == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed initial gcd_seq calculation and proof logic */
    assert(values@.len() >= 1);
    assert(values@[0] > 0);
    let mut result = values[0];
    let mut i: usize = 1;
    
    assert(result > 0);
    assert(gcd_seq(values_as_int(values@), 1, values@[0] as int) == gcd_seq(values_as_int(values@), 1, result as int));
    
    while i < values.len()
        invariant
            1 <= i <= values.len(),
            result > 0,
            result as int == gcd_seq(values_as_int(values@), i as int, values@[0] as int),
            forall|k: int| 0 <= k < i ==> (values@[k] as int) % (result as int) == 0,
        decreases values.len() - i,
    {
        proof {
            assert(values@[i as int] > 0);
            gcd_positive(result as int, values@[i as int] as int);
            let next_gcd = gcd(result as int, values@[i as int] as int);
            assert(next_gcd > 0);
            
            assert(gcd_seq(values_as_int(values@), i as int, values@[0] as int) == result as int);
            assert(gcd_seq(values_as_int(values@), (i + 1) as int, values@[0] as int) == 
                   gcd_seq(values_as_int(values@), (i + 1) as int, gcd(values@[0] as int, values@[1] as int))) by {
                if i == 1 {
                    assert(result as int == values@[0] as int);
                    assert(next_gcd == gcd(values@[0] as int, values@[1] as int));
                }
            };
            
            assert forall|k: int| 0 <= k < i implies (values@[k] as int) % next_gcd == 0 by {
                if k == 0 {
                    assert(result as int == gcd_seq(values_as_int(values@), i as int, values@[0] as int));
                    gcd_seq_divides_all(values_as_int(values@), i as int, result as int, 0);
                    assert(values@[0] as int % result as int == 0);
                    gcd_divides_both(result as int, values@[i as int] as int);
                    assert(result as int % next_gcd == 0);
                    let q = result as int / next_gcd;
                    assert(result as int == q * next_gcd);
                    if values@[0] as int % result as int == 0 {
                        let p = values@[0] as int / result as int;
                        assert(values@[0] as int == p * result as int);
                        assert(values@[0] as int == p * q * next_gcd);
                        assert(values@[0] as int % next_gcd == 0);
                    }
                } else {
                    assert((values@[k] as int) % (result as int) == 0);
                    gcd_divides_both(result as int, values@[i as int] as int);
                    assert(result as int % next_gcd == 0);
                    let q = result as int / next_gcd;
                    assert(result as int == q * next_gcd);
                    let p = values@[k] as int / result as int;
                    assert(values@[k] as int == p * result as int);
                    assert(values@[k] as int == p * q * next_gcd);
                    assert(values@[k] as int % next_gcd == 0);
                }
            };
            
            gcd_divides_both(result as int, values@[i as int] as int);
            assert(values@[i as int] as int % next_gcd == 0);
        }
        
        result = gcd_exec(result, values[i]);
        i = i + 1;
    }
    
    proof {
        assert(i == values.len());
        assert(result as int == gcd_seq(values_as_int(values@), values@.len() as int, values@[0] as int));
        assert(gcd_of_all(values_as_int(values@)) == gcd_seq(values_as_int(values@), 1, values@[0] as int));
        
        assert forall|k: int| 0 <= k < values@.len() implies (values@[k] as int) % (result as int) == 0 by {
            assert((values@[k] as int) % (result as int) == 0);
        };
    }
    
    result
}
// </vc-code>


}

fn main() {}