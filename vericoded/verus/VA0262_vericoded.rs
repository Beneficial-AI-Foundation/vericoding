// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn get_category(hp: int) -> char {
        let remainder = hp % 4;
        if remainder == 1 {
            'A'
        } else if remainder == 3 {
            'B'
        } else if remainder == 2 {
            'C'
        } else {
            'D'
        }
    }
    
    spec fn valid_input(n: int) -> bool {
        30 <= n <= 100
    }
    
    spec fn valid_output(a: int, b: char) -> bool {
        0 <= a <= 2 && (b == 'A' || b == 'B' || b == 'C' || b == 'D')
    }
    
    spec fn optimal_choice(n: int, a: int, b: char) -> bool {
        b == get_category(n + a) &&
        ((n % 4 == 1) ==> (a == 0 && b == 'A')) &&
        ((n % 4 == 2) ==> (a == 1 && b == 'B')) &&
        ((n % 4 == 3) ==> (a == 2 && b == 'A')) &&
        ((n % 4 == 0) ==> (a == 1 && b == 'A'))
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added explicit int suffixes for literals to avoid type inference issues */
proof fn mod4_add1_from_rem0(x: int)
    requires
        x % 4int == 0int,
    ensures
        (x + 1int) % 4int == 1int,
{
    assert(((x + 1int) % 4int) == ((x % 4int) + (1int % 4int)) % 4int);
    assert(x % 4int == 0int);
    assert(1int % 4int == 1int);
    assert(((x % 4int) + (1int % 4int)) % 4int == (0int + 1int) % 4int);
    assert((0int + 1int) % 4int == 1int);
}

/* helper modified by LLM (iteration 3): added explicit int suffixes for literals to avoid type inference issues */
proof fn mod4_add1_from_rem2(x: int)
    requires
        x % 4int == 2int,
    ensures
        (x + 1int) % 4int == 3int,
{
    assert(((x + 1int) % 4int) == ((x % 4int) + (1int % 4int)) % 4int);
    assert(x % 4int == 2int);
    assert(1int % 4int == 1int);
    assert(((x % 4int) + (1int % 4int)) % 4int == (2int + 1int) % 4int);
    assert((2int + 1int) % 4int == 3int);
}

/* helper modified by LLM (iteration 3): added explicit int suffixes for literals to avoid type inference issues */
proof fn mod4_add2_from_rem3(x: int)
    requires
        x % 4int == 3int,
    ensures
        (x + 2int) % 4int == 1int,
{
    assert(((x + 2int) % 4int) == ((x % 4int) + (2int % 4int)) % 4int);
    assert(x % 4int == 3int);
    assert(2int % 4int == 2int);
    assert(((x % 4int) + (2int % 4int)) % 4int == (3int + 2int) % 4int);
    assert((3int + 2int) % 4int == 1int);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: (i8, char))
    requires 
        30 <= n <= 100
    ensures 
        0 <= result.0 <= 2 && (result.1 == 'A' || result.1 == 'B' || result.1 == 'C' || result.1 == 'D'),
        optimal_choice(n as int, result.0 as int, result.1),
        result.1 == 'A' || result.1 == 'B'
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed integer literal suffixes in proofs and tightened modulo reasoning */
    let r: i8 = n % 4i8;
    let a: i8;
    let b: char;
    if r == 1 {
        a = 0;
        b = 'A';
        proof {
            assert(((n % 4i8) as int) == (n as int) % 4int);
            assert((r as int) == ((n % 4i8) as int));
            assert((n as int) % 4int == (r as int));
            assert((n as int) % 4int == 1int);
            assert(a as int == 0int);
            assert((n as int) + (a as int) == (n as int));
            assert(((n as int) + (a as int)) % 4int == (n as int) % 4int);
            assert(get_category((n as int) + (a as int)) == 'A');
        }
    } else if r == 2 {
        a = 1;
        b = 'B';
        proof {
            assert(((n % 4i8) as int) == (n as int) % 4int);
            assert((r as int) == ((n % 4i8) as int));
            assert((n as int) % 4int == (r as int));
            assert((n as int) % 4int == 2int);
            mod4_add1_from_rem2(n as int);
            assert(((n as int) + (a as int)) % 4int == 3int);
            assert(get_category((n as int) + (a as int)) == 'B');
        }
    } else if r == 3 {
        a = 2;
        b = 'A';
        proof {
            assert(((n % 4i8) as int) == (n as int) % 4int);
            assert((r as int) == ((n % 4i8) as int));
            assert((n as int) % 4int == (r as int));
            assert((n as int) % 4int == 3int);
            mod4_add2_from_rem3(n as int);
            assert(((n as int) + (a as int)) % 4int == 1int);
            assert(get_category((n as int) + (a as int)) == 'A');
        }
    } else {
        a = 1;
        b = 'A';
        proof {
            assert(((n % 4i8) as int) == (n as int) % 4int);
            assert((r as int) == ((n % 4i8) as int));
            assert((n as int) % 4int == (r as int));
            assert((n as int) % 4int == 0int);
            mod4_add1_from_rem0(n as int);
            assert(((n as int) + (a as int)) % 4int == 1int);
            assert(get_category((n as int) + (a as int)) == 'A');
        }
    }

    proof {
        assert(0int <= (a as int) && (a as int) <= 2int);
        assert(b == 'A' || b == 'B');
        assert(optimal_choice(n as int, a as int, b));
    }
    (a, b)
}
// </vc-code>

}

fn main() {}