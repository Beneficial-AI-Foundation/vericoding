// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    k >= 1 && n >= 1 && k <= n
}

spec fn total_moves(n: int, k: int) -> int {
    if valid_input(n, k) { n / k } else { 0 }
}

spec fn first_player_wins(n: int, k: int) -> bool {
    if valid_input(n, k) { total_moves(n, k) % 2 == 1 } else { false }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Division lemma ensuring (t*k + r)/k == t when 0 <= r < k and k >= 1 */
proof fn lemma_div_mul_plus_rem(k: int, t: int, r: int)
    requires
        k >= 1,
        t >= 0,
        0 <= r,
        r < k,
    ensures
        (t * k + r) / k == t,
{
    // Show t*k <= t*k + r < (t+1)*k so the quotient is t
    assert(t * k <= t * k + r);
    assert((t + 1) * k == t * k + k);
    assert(t * k + r < (t + 1) * k);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: String)
    requires
        valid_input(n as int, k as int),
    ensures
        first_player_wins(n as int, k as int) ==> result@ == seq!['Y', 'E', 'S'],
        !first_player_wins(n as int, k as int) ==> result@ == seq!['N', 'O'],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): compute steps via subtraction loop, prove quotient equals steps, return String::from("YES"/"NO") */
{
    let mut rem: i8 = n;
    let mut steps: i8 = 0;

    while (rem as int) >= (k as int)
        invariant
            valid_input(n as int, k as int),
            0 <= rem as int,
            0 <= steps as int,
            n as int == (steps as int) * (k as int) + (rem as int),
        decreases rem as int
    {
        rem = rem - k;
        steps = steps + 1;
    }

    proof {
        let n_int = n as int;
        let k_int = k as int;
        let steps_int = steps as int;
        let rem_int = rem as int;
        assert(rem_int >= 0);
        assert(rem_int < k_int); // from loop exit condition
        assert(n_int == steps_int * k_int + rem_int);
        lemma_div_mul_plus_rem(k_int, steps_int, rem_int);
        assert(n_int / k_int == steps_int);
    }

    let wins = ((steps as int) % 2 == 1);
    let result: String = if wins {
        std::string::String::from("YES")
    } else {
        std::string::String::from("NO")
    };
    result
}
// </vc-code>


}

fn main() {}