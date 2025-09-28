// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * power(x, (y - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_power_increases(x: nat, y: nat)
    requires x >= 1
    ensures 
        x == 1 ==> power(x, y) == 1,
        x > 1 ==> power(x, y) >= x.pow(y as u32),
        power(x, y) >= 1
    decreases y
{
    /* helper modified by LLM (iteration 5): Fixed postcondition for all x >= 1 */
    if y == 0 {
        assert(power(x, 0) == 1);
    } else {
        lemma_power_increases(x, (y - 1) as nat);
        assert(power(x, y) == x * power(x, (y - 1) as nat));
        if x == 1 {
            assert(power(x, (y - 1) as nat) == 1);
            assert(power(x, y) == 1);
        } else {
            assert(x > 1);
            assert(power(x, (y - 1) as nat) >= 1);
            assert(power(x, y) >= x);
        }
    }
}

proof fn lemma_power_monotonic(x: nat, y1: nat, y2: nat)
    requires 
        x >= 1,
        y1 <= y2
    ensures power(x, y1) <= power(x, y2)
    decreases y2 - y1
{
    /* helper modified by LLM (iteration 5): Fixed to handle x >= 1 */
    if y1 == y2 {
        assert(power(x, y1) == power(x, y2));
    } else {
        lemma_power_monotonic(x, y1, (y2 - 1) as nat);
        assert(power(x, y2) == x * power(x, (y2 - 1) as nat));
        assert(power(x, y1) <= power(x, (y2 - 1) as nat));
        if x == 0 {
            assert(power(x, y2) == 0);
        } else {
            assert(x >= 1);
            assert(power(x, y2) >= power(x, (y2 - 1) as nat));
        }
    }
}

proof fn lemma_power_strictly_increases(x: nat, y: nat)
    requires x > 1
    ensures 
        y > 0 ==> power(x, y) > power(x, (y - 1) as nat),
        power(x, y) >= 1
    decreases y
{
    /* helper modified by LLM (iteration 5): Fixed postconditions */
    if y == 0 {
        assert(power(x, 0) == 1);
    } else {
        lemma_power_strictly_increases(x, (y - 1) as nat);
        assert(power(x, y) == x * power(x, (y - 1) as nat));
        assert(power(x, (y - 1) as nat) >= 1);
        assert(x > 1);
        assert(power(x, y) > power(x, (y - 1) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn is_simple_power(x: u8, n: i8) -> (ans: bool)
    requires x > 0
    ensures ans <==> exists|y: nat| n as int == power(x as nat, y) as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type casting issues with nat/int in executable code */
    if n <= 0 {
        assert(forall|y: nat| power(x as nat, y) >= 1);
        assert(!exists|y: nat| n as int == power(x as nat, y) as int);
        return false;
    }
    
    if n == 1 {
        assert(power(x as nat, 0) == 1);
        assert(exists|y: nat| n as int == power(x as nat, y) as int) by {
            assert(n as int == power(x as nat, 0) as int);
        };
        return true;
    }
    
    if x == 1 {
        lemma_power_increases(1, 0);
        assert(forall|y: nat| power(1, y) == 1);
        assert(!exists|y: nat| n as int == power(1, y) as int);
        return false;
    }
    
    assert(x > 1);
    assert(n > 1);
    
    let mut current: u8 = 1;
    let mut y_candidate: u8 = 0;
    
    while current < n as u8 && current <= u8::MAX / x
        invariant
            x > 1,
            current == power(x as nat, y_candidate as nat),
            current >= 1,
            forall|y: nat| y < y_candidate ==> power(x as nat, y) < n,
            current <= u8::MAX
    {
        let next = current * x;
        current = next;
        y_candidate = y_candidate + 1;
        
        assert(current == power(x as nat, y_candidate as nat));
        proof {
            lemma_power_strictly_increases(x as nat, y_candidate as nat);
        }
    }
    
    if current == n as u8 {
        assert(exists|y: nat| n as int == power(x as nat, y) as int) by {
            assert(n as int == power(x as nat, y_candidate as nat) as int);
        };
        return true;
    } else {
        if current > u8::MAX / x {
            assert(power(x as nat, (y_candidate + 1) as nat) > u8::MAX);
            assert(power(x as nat, y_candidate as nat) < n);
            assert(!exists|y: nat| n as int == power(x as nat, y) as int);
        } else {
            assert(current as int > n as int);
            assert(power(x as nat, y_candidate as nat) > n);
            if y_candidate > 0 {
                assert(power(x as nat, (y_candidate - 1) as nat) < n);
            }
            assert(!exists|y: nat| n as int == power(x as nat, y) as int);
        }
        return false;
    }
}
// </vc-code>


}

fn main() {}