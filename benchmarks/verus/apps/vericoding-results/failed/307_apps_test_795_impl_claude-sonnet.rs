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
exec fn extract_integer_impl(input: Vec<char>) -> (result: int)
    requires
        valid_input(input@),
    ensures
        result == extract_integer(input@),
{
    let mut result = 0;
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            result == extract_integer(input@.subrange(0, i as int)),
    {
        if input[i].is_ascii_digit() {
            let digit_val = (input[i] as u8 - b'0') as usize;
            result = result * 10 + digit_val;
        }
        i += 1;
    }
    result
}

exec fn integer_square_root_impl(n: int) -> (result: int)
    requires
        valid_n(n),
    ensures
        result == integer_square_root(n),
        result * result <= n,
        (result + 1) * (result + 1) > n,
{
    let mut x = 1;
    while (x + 1) * (x + 1) <= n
        invariant
            x >= 1,
            x * x <= n,
        decreases n - x * x
    {
        x += 1;
    }
    x
}

exec fn count_from_primitives_impl(n: int, m: int, u: int, v: int) -> (result: int)
    requires
        valid_n(n),
        m == integer_square_root(n),
        u >= 1,
        v >= 1,
    ensures
        result == count_from_primitives(n, m, u, v),
{
    if u > m {
        0
    } else if v > u {
        count_from_primitives_impl(n, m, u + 1, 1)
    } else {
        let a = u * u - v * v;
        let b = 2 * u * v;
        let c = u * u + v * v;
        let count = if a * a + b * b == c * c && c <= n { 1 } else { 0 };
        count + count_from_primitives_impl(n, m, u, v + 1)
    }
}

exec fn int_to_string_impl(n: int) -> (result: Vec<char>)
    ensures
        result@ == int_to_string(n),
        result@.len() > 0,
{
    if n == 0 {
        vec!['0']
    } else {
        let mut digits = Vec::new();
        let mut num = n;
        while num > 0
            invariant
                num >= 0,
        {
            let digit = (num % 10) as u8 + b'0';
            digits.push(digit as char);
            num = num / 10;
        }
        digits.reverse();
        digits
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
    /* code modified by LLM (iteration 5): remove explicit int cast */
    let n = extract_integer_impl(stdin_input);
    let count = {
        let m = integer_square_root_impl(n);
        count_from_primitives_impl(n, m, 1, 1)
    };
    int_to_string_impl(count)
}
// </vc-code>


}

fn main() {}