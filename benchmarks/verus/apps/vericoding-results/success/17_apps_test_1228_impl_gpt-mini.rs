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
/* helper modified by LLM (iteration 3): choose a based on n mod 4 */
spec fn choose_a(n: int) -> int {
    if n % 4 == 1 {
        0
    } else if n % 4 == 2 {
        1
    } else if n % 4 == 3 {
        2
    } else {
        1
    }
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
    /* code modified by LLM (iteration 3): compute a and b from n%4 and prove optimal_choice */
    let a_i8: i8 = if n % 4 == 1 {
        0
    } else if n % 4 == 2 {
        1
    } else if n % 4 == 3 {
        2
    } else {
        1
    };
    let rem: i8 = (n + a_i8) % 4;
    let b: char = if rem == 1 {
        'A'
    } else if rem == 3 {
        'B'
    } else if rem == 2 {
        'C'
    } else {
        'D'
    };
    proof {
        let n_int: int = n as int;
        let a_int: int = a_i8 as int;
        if n_int % 4 == 1 {
            assert(a_int == 0);
            assert((n_int + a_int) % 4 == 1);
            assert(b == 'A');
        } else if n_int % 4 == 2 {
            assert(a_int == 1);
            assert((n_int + a_int) % 4 == 3);
            assert(b == 'B');
        } else if n_int % 4 == 3 {
            assert(a_int == 2);
            assert((n_int + a_int) % 4 == 1);
            assert(b == 'A');
        } else {
            assert(a_int == 1);
            assert((n_int + a_int) % 4 == 1);
            assert(b == 'A');
        }
        assert(b == get_category(n_int + a_int));
        assert((n_int % 4 == 1) ==> (a_int == 0 && b == 'A'));
        assert((n_int % 4 == 2) ==> (a_int == 1 && b == 'B'));
        assert((n_int % 4 == 3) ==> (a_int == 2 && b == 'A'));
        assert((n_int % 4 == 0) ==> (a_int == 1 && b == 'A'));
        assert(optimal_choice(n_int, a_int, b));
        assert(0 <= a_int && a_int <= 2);
        assert(b == 'A' || b == 'B');
    }
    (a_i8, b)
}
// </vc-code>

}

fn main() {}