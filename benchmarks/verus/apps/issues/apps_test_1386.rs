// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    exists|i: int| 0 < i < input.len() - 1 && input[i] == ' ' &&
    (forall|j: int| 0 <= j < i ==> '0' <= input[j] <= '9') &&
    (forall|j: int| i < j < input.len() ==> '0' <= input[j] <= '9')
}

spec fn valid_dimensions(w: int, h: int) -> bool {
    w >= 1 && h >= 1 && w <= 1000 && h <= 1000
}

spec fn parse_two_ints(input: Seq<char>) -> (int, int) {
    let space_index = find_space_spec(input, 0);
    let w = string_to_int_spec(input.subrange(0, space_index));
    let h = string_to_int_spec(input.subrange(space_index + 1, input.len() as int));
    (w, h)
}

spec fn find_space_spec(s: Seq<char>, start: int) -> int
    decreases s.len() - start
{
    if s[start] == ' ' {
        start
    } else {
        find_space_spec(s, start + 1)
    }
}

spec fn string_to_int_spec(s: Seq<char>) -> int {
    if s.len() == 1 {
        s[0] as int - '0' as int
    } else {
        string_to_int_spec(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] as int - '0' as int)
    }
}

spec fn int_to_string_spec(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string_spec(n / 10).add(int_to_string_spec(n % 10))
    }
}

spec fn mod_pow_spec(base: int, exp: int, mod_val: int) -> int {
    if exp == 0 {
        1int % mod_val
    } else if exp % 2 == 0 {
        let half = mod_pow_spec(base, exp / 2, mod_val);
        (half * half) % mod_val
    } else {
        (base * mod_pow_spec(base, exp - 1, mod_val)) % mod_val
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn main_function() -> (result: int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}