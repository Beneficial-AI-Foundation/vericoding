// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> 
        s[i] == ' ' || s[i] == '\n' || ('0' <= s[i] <= '9') || s[i] == '-')
}

spec fn valid_number(s: Seq<char>) -> bool {
    s.len() == 0 || (forall|i: int| 0 <= i < s.len() ==> 
        '0' <= s[i] <= '9' || (i == 0 && s[i] == '-'))
}

spec fn count_zeros(numbers: Seq<int>) -> int
    decreases numbers.len()
{
    if numbers.len() == 0 { 
        0
    } else { 
        (if numbers[0] == 0 { 1 } else { 0 }) + count_zeros(numbers.subrange(1, numbers.len() as int))
    }
}

spec fn find_zero_index(numbers: Seq<int>) -> int {
    requires([
        numbers.len() > 0,
        count_zeros(numbers) == 1,
    ]);
    decreases(numbers.len());
    
    if numbers[0] == 0 { 
        0
    } else if numbers.len() > 1 { 
        1 + find_zero_index(numbers.subrange(1, numbers.len() as int))
    } else { 
        0
    }
}

spec fn parse_ints(s: Seq<char>) -> Seq<int> {
    requires([
        s.len() > 0,
        valid_input(s),
    ]);
    
    parse_ints_helper(s, 0, seq![], seq![])
}

spec fn parse_ints_helper(s: Seq<char>, pos: int, current: Seq<char>, result: Seq<int>) -> Seq<int>
    decreases s.len() - pos
{
    if pos >= s.len() { 
        if current.len() > 0 { result.push(0) } else { result }
    } else if s[pos] == ' ' || s[pos] == '\n' {
        if current.len() > 0 { 
            parse_ints_helper(s, pos + 1, seq![], result.push(0))
        } else { 
            parse_ints_helper(s, pos + 1, current, result)
        }
    } else {
        parse_ints_helper(s, pos + 1, current.push(s[pos]), result)
    }
}

spec fn generate_output(numbers: Seq<int>) -> Seq<char> {
    generate_output_helper(numbers, 0, seq![])
}

spec fn generate_output_helper(numbers: Seq<int>, pos: int, result: Seq<char>) -> Seq<char>
    decreases numbers.len() - pos
{
    if pos >= numbers.len() { 
        result
    } else if numbers[pos] == 0 { 
        seq_to_string(pos + 1)
    } else { 
        generate_output_helper(numbers, pos + 1, result)
    }
}

spec fn seq_to_string(n: int) -> Seq<char> {
    if n == 0 { 
        seq!['0']
    } else if n < 10 { 
        seq![char::from_u8((n + 48) as u8)]
    } else { 
        seq_to_string(n / 10).add(seq![char::from_u8(((n % 10) + 48) as u8)])
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String) {
    requires([
        valid_input(input@),
        input@.len() > 0,
    ]);
    ensures(|result: String| {
        let numbers = parse_ints(input@);
        result@ == generate_output(numbers)
    });
// </vc-spec>
// <vc-code>
// impl-start
assume(false);
String::new()
// impl-end
// </vc-code>

}

}

fn main() {}