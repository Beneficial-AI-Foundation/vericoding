// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_n(n: int) -> bool {
    n >= 1 && n <= 10000
}

spec fn integer_square_root(n: int) -> int {
    0  /* placeholder implementation */
}

spec fn count_from_primitives(n: int, m: int, u: int, v: int) -> int {
    0  /* placeholder implementation */
}

spec fn extract_integer(input: Seq<char>) -> int {
    0  /* placeholder implementation */
}

spec fn int_to_string(n: int) -> Seq<char> {
    seq![]  /* placeholder implementation */
}

spec fn count_pythagorean_triples_via_primitives(n: int) -> int {
    let m = integer_square_root(n);
    count_from_primitives(n, m, 1, 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added gcd helper */
spec fn gcd(a: int, b: int) -> int
    decreases a as nat + b as nat
{
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/* helper modified by LLM (iteration 5): added count_for_m helper */
spec fn count_for_m(n: int, u: int, v: int, nval: int) -> int
    decreases (u - nval)
{
    if nval > u - 1 {
        0
    } else {
        let a = u * u - nval * nval;
        let b = 2 * u * nval;
        let c = u * u + nval * nval;
        let conditions = ((u - nval) % 2 == 1) && (nval > v) && gcd(u, nval) == 1;
        if conditions && (c <= n) {
            1 + count_for_m(n, u, v, nval + 1)
        } else {
            count_for_m(n, u, v, nval + 1)
        }
    }
}

/* helper modified by LLM (iteration 5): fixed integer_square_root implementation */
spec fn integer_square_root(n: int) -> int
{
    if n < 0 {
        0
    } else {
        choose |s: int| (s >= 0) && (s * s <= n) && ((s + 1) * (s + 1) > n)
    }
}

/* helper modified by LLM (iteration 5): fixed count_from_primitives implementation */
spec fn count_from_primitives(n: int, m: int, u: int, v: int) -> int
    decreases m - u
{
    if u > m {
        0
    } else {
        count_for_m(n, u, v, v) + count_from_primitives(n, m, u + 1, v)
    }
}

/* helper modified by LLM (iteration 5): fixed extract_integer implementation */
spec fn extract_integer(input: Seq<char>) -> int
    decreases input.len()
{
    if input.len() == 0 {
        0
    } else if ('0' <= input[0]) && (input[0] <= '9') {
        (input[0] as int - '0' as int) + 10 * extract_integer(input.subrange(1, input.len()))
    } else {
        0
    }
}

/* helper modified by LLM (iteration 5): fixed int_to_string implementation */
spec fn int_to_string(n: int) -> Seq<char>
    decreases n as nat
{
    if n == 0 {
        seq!['0']
    } else {
        let digit = (('0' as int) + (n % 10)) as char;
        if n / 10 == 0 {
            seq![digit]
        } else {
            let s = int_to_string(n / 10);
            s + seq![digit]
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures 
        result@.len() > 0,
        result@ == int_to_string(count_pythagorean_triples_via_primitives(extract_integer(stdin_input@)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): updated to use fixed helper functions */
    let n = extract_integer(stdin_input@);
    let m = integer_square_root(n);
    let count = count_from_primitives(n, m, 1, 1);
    let seq = int_to_string(count);
    let mut result: Vec<char> = Vec::new();
    let mut i = 0;
    proof {
        assert(result@ == seq.subrange(0, 0));
    }
    while i < seq.len()
        invariant
            i <= seq.len(),
            result@.len() == i,
            result@ == seq.subrange(0, i)
    {
        result.push(seq[i]);
        i = i + 1;
        proof {
            assert(result@ == seq.subrange(0, i));
        }
    }
    result
}
// </vc-code>


}

fn main() {}