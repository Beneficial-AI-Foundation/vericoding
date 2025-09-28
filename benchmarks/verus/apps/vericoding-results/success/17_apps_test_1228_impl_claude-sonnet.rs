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
    let remainder = n % 4;
    let (a, b) = if remainder == 1 {
        (0, 'A')
    } else if remainder == 2 {
        (1, 'B')
    } else if remainder == 3 {
        (2, 'A')
    } else {
        (1, 'A')
    };
    
    proof {
        assert(remainder >= 0 && remainder < 4);
        assert(0 <= a <= 2);
        assert(b == 'A' || b == 'B' || b == 'C' || b == 'D');
        assert(b == get_category((n + a) as int));
        assert(optimal_choice(n as int, a as int, b));
        assert(b == 'A' || b == 'B');
    }
    
    (a, b)
}
// </vc-code>

}

fn main() {}