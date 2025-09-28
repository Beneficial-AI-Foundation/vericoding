// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    true /* Simplified for now */
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0
}

spec fn split_string_func(s: Seq<char>) -> Seq<Seq<char>> {
    seq![seq!['1'], seq!['2'], seq!['3']] /* Simplified for now */
}

spec fn string_to_int_func(s: Seq<char>) -> int {
    if s.len() > 0 && s[0] == '1' { 1 }
    else if s.len() > 0 && s[0] == '2' { 2 }
    else if s.len() > 0 && s[0] == '3' { 3 }
    else { 0 }
}

spec fn int_to_string_func(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else if n == 2 { seq!['2'] }
    else if n == 3 { seq!['3'] }
    else { seq!['0'] }
}

spec fn min_parking_cost(n: int, a: int, b: int) -> int {
    let plan1_cost = n * a;
    let plan2_cost = b;
    if plan1_cost <= plan2_cost { plan1_cost } else { plan2_cost }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_split_string_valid(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        split_string_func(s).len() == 3,
        is_valid_integer(split_string_func(s)[0]),
        is_valid_integer(split_string_func(s)[1]),
        is_valid_integer(split_string_func(s)[2])
{
}

proof fn lemma_string_to_int_valid(s: Seq<char>)
    requires
        is_valid_integer(s),
    ensures
        string_to_int_func(s) >= 0
{
}

proof fn lemma_min_parking_cost_properties(n: int, a: int, b: int)
    requires
        n >= 0,
        a >= 0,
        b >= 0,
    ensures
        min_parking_cost(n, a, b) >= 0
{
}

fn parse_integer(s: &str) -> (result: u64)
    requires
        s@.len() > 0,
        is_valid_integer(s@),
    ensures
        result as int == string_to_int_func(s@),
        result >= 0
{
    let mut res: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            res as int == string_to_int_func(s@.subrange(0, i as int)),
            res >= 0
        decreases s.len() - i
    {
        let c = s.as_bytes()[i] as char;
        let digit_value = (c as u64) - ('0' as u64);
        res = res * 10 + digit_value;
        i += 1;
    }
    
    res
}

fn integer_to_string(n: u64) -> (result: String)
    requires
        n >= 0,
    ensures
        result@ == int_to_string_func(n as int)
{
    if n == 0 {
        String::from("0")
    } else {
        let mut num = n;
        let mut digits: Vec<char> = Vec::new();
        
        while num > 0
            invariant
                num >= 0,
                int_to_string_func(num as int) + digits@ == int_to_string_func(n as int)
            decreases num
        {
            let digit = (num % 10) as u8;
            digits.push((digit + b'0') as char);
            num /= 10;
        }
        
        digits.reverse();
        let mut result_str = String::with_capacity(digits.len() as usize);
        for c in &digits {
            result_str.push(*c);
        }
        result_str
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires
        input.len() > 0,
        valid_input(input),
    ensures
        ({
            let parts = split_string_func(input);
            let n = string_to_int_func(parts[0]);
            let a = string_to_int_func(parts[1]);
            let b = string_to_int_func(parts[2]);
            result == int_to_string_func(min_parking_cost(n, a, b)) + seq!['\n']
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type conversions and indexing */
    proof {
        lemma_split_string_valid(input);
    }
    
    let mut input_str = String::with_capacity(input.len() as usize);
    for i in 0usize..input.len() as usize {
        input_str.push(input[i as int]);
    }
    
    let parts: Vec<&str> = input_str.split_whitespace().collect();
    
    proof {
        assert(parts@.len() == 3) by {
            lemma_split_string_valid(input);
        };
    }
    
    let n_u64 = parse_integer(parts[0]);
    let a_u64 = parse_integer(parts[1]);
    let b_u64 = parse_integer(parts[2]);
    
    proof {
        lemma_min_parking_cost_properties(n_u64 as int, a_u64 as int, b_u64 as int);
    }
    
    let n: u64 = n_u64;
    let a: u64 = a_u64;
    let b: u64 = b_u64;
    let cost = if n * a <= b { n * a } else { b };
    let result_str = integer_to_string(cost) + "\n";
    
    let mut result_seq = Seq::empty();
    for c in result_str.chars() {
        result_seq = result_seq.push(c);
    }
    result_seq
}
// </vc-code>


}

fn main() {}