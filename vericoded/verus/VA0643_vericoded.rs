// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    100 <= n <= 999
}

spec fn valid_output(n: int, result: Seq<char>) -> bool
    recommends valid_input(n)
{
    result.len() == 6 && result.subrange(0, 3) == seq!['A', 'B', 'C'] && result.subrange(3, result.len() as int) == int_to_string(n)
}

spec fn int_to_string(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        seq![('0' as u8 + n as u8) as char]
    } else {
        int_to_string(n / 10).add(seq![('0' as u8 + (n % 10) as u8) as char])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): helpers for converting digits to chars and proving int_to_string structure */
spec fn char_of_digit(d: int) -> char
    recommends
        0 <= d < 10
{
    ('0' as u8 + d as u8) as char
}

/* helper modified by LLM (iteration 2): lemma for single-digit conversion */
proof fn lemma_int_to_string_single_digit(d: int)
    requires
        0 <= d < 10,
    ensures
        int_to_string(d) == seq![char_of_digit(d)],
{
    assert(int_to_string(d) == seq![('0' as u8 + d as u8) as char]);
}

/* helper modified by LLM (iteration 2): lemma for two-digit conversion */
proof fn lemma_int_to_string_two_digits(n: int)
    requires
        10 <= n < 100,
    ensures
        int_to_string(n) == seq![char_of_digit(n / 10), char_of_digit(n % 10)],
{
    assert(1 <= n / 10 && n / 10 < 10);
    assert(0 <= n % 10 && n % 10 < 10);

    assert(int_to_string(n) == int_to_string(n / 10).add(seq![('0' as u8 + (n % 10) as u8) as char]));
    lemma_int_to_string_single_digit(n / 10);
    assert(int_to_string(n / 10) == seq![char_of_digit(n / 10)]);
    assert(seq![('0' as u8 + (n % 10) as u8) as char] == seq![char_of_digit(n % 10)]);
    assert(int_to_string(n) == seq![char_of_digit(n / 10)].add(seq![char_of_digit(n % 10)]));
    assert(seq![char_of_digit(n / 10)].add(seq![char_of_digit(n % 10)]) == seq![char_of_digit(n / 10), char_of_digit(n % 10)]);
}

/* helper modified by LLM (iteration 2): lemma for three-digit conversion */
proof fn lemma_int_to_string_three_digits(n: int)
    requires
        100 <= n < 1000,
    ensures
        int_to_string(n) == seq![char_of_digit(n / 100), char_of_digit((n / 10) % 10), char_of_digit(n % 10)],
{
    assert(10 <= n / 10 && n / 10 < 100);
    assert(0 <= n % 10 && n % 10 < 10);
    assert(int_to_string(n) == int_to_string(n / 10).add(seq![('0' as u8 + (n % 10) as u8) as char]));

    lemma_int_to_string_two_digits(n / 10);
    assert(int_to_string(n / 10) == seq![char_of_digit((n / 10) / 10), char_of_digit((n / 10) % 10)]);
    assert((n / 10) / 10 == n / 100);
    assert(seq![('0' as u8 + (n % 10) as u8) as char] == seq![char_of_digit(n % 10)]);

    assert(int_to_string(n)
        == seq![char_of_digit(n / 100), char_of_digit((n / 10) % 10)].add(seq![char_of_digit(n % 10)]));
    assert(seq![char_of_digit(n / 100), char_of_digit((n / 10) % 10)].add(seq![char_of_digit(n % 10)])
        == seq![char_of_digit(n / 100), char_of_digit((n / 10) % 10), char_of_digit(n % 10)]);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures valid_output(n as int, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): avoid exec 'int' usage; compute digits with i32 and connect via proof */
    let mut result: Vec<char> = Vec::new();
    result.push('A');
    result.push('B');
    result.push('C');

    let ni: i32 = n as i32;

    let d1_i32: i32 = ni / 100;
    let d2_i32: i32 = (ni / 10) % 10;
    let d3_i32: i32 = ni % 10;

    let c1: char = ('0' as u8 + (d1_i32 as u8)) as char;
    let c2: char = ('0' as u8 + (d2_i32 as u8)) as char;
    let c3: char = ('0' as u8 + (d3_i32 as u8)) as char;

    result.push(c1);
    result.push(c2);
    result.push(c3);

    proof {
        let gi: int = n as int;
        assert(100 <= gi && gi < 1000);
        assert(1 <= gi / 100 && gi / 100 < 10);
        assert(10 <= gi / 10 && gi / 10 < 100);
        assert(0 <= (gi / 10) % 10 && (gi / 10) % 10 < 10);
        assert(0 <= gi % 10 && gi % 10 < 10);

        // Relate runtime digit computations with ghost math digits
        assert((d1_i32 as int) == gi / 100);
        assert((d2_i32 as int) == (gi / 10) % 10);
        assert((d3_i32 as int) == gi % 10);

        // Map runtime chars to spec char_of_digit
        assert(c1 == char_of_digit(gi / 100));
        assert(c2 == char_of_digit((gi / 10) % 10));
        assert(c3 == char_of_digit(gi % 10));

        // Use structural lemma about int_to_string for three-digit numbers
        lemma_int_to_string_three_digits(gi);
        assert(seq![c1, c2, c3] == int_to_string(gi));

        // Structural facts about the constructed vector
        assert(result@ == seq!['A', 'B', 'C', c1, c2, c3]);
        assert(result@.subrange(0, 3) == seq!['A', 'B', 'C']);
        assert(result@.len() == 6);
        assert(result@.subrange(3, result@.len() as int) == seq![c1, c2, c3]);
    }

    result
}
// </vc-code>


}

fn main() {}