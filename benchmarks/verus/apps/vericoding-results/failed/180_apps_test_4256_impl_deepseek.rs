// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    exists|i: int, j: int| 0 <= i < j < input.len() && input[i] == ' ' && input[j] == ' ' &&
    ({
        let parts = split_string_spec(input);
        parts.len() >= 3 && 
        is_valid_integer(parts[0]) && is_valid_integer(parts[1]) && is_valid_integer(parts[2]) &&
        ({
            let a = string_to_int_spec(parts[0]);
            let b = string_to_int_spec(parts[1]);
            let c = string_to_int_spec(parts[2]);
            1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
        })
    })
}

spec fn compute_drinks(a: int, b: int, c: int) -> int {
    if b / a < c { b / a } else { c }
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && s[i] <= '9'
}

spec fn string_to_int_spec(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 1 { 
        s[0] as int - '0' as int
    } else if s.len() > 1 { 
        string_to_int_spec(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] as int - '0' as int)
    } else {
        0
    }
}

spec fn split_string_spec(s: Seq<char>) -> Seq<Seq<char>> {
    if s.len() == 0 { 
        seq![] 
    } else {
        split_helper(s, 0, seq![])
    }
}

spec fn split_helper(s: Seq<char>, index: int, current: Seq<char>) -> Seq<Seq<char>>
    decreases s.len() - index
{
    if index >= s.len() {
        if current.len() > 0 { seq![current] } else { seq![] }
    } else if s[index] == ' ' || s[index] == '\n' || s[index] == '\t' {
        if current.len() > 0 { 
            seq![current] + split_helper(s, index + 1, seq![])
        } else { 
            split_helper(s, index + 1, seq![])
        }
    } else {
        split_helper(s, index + 1, current.push(s[index]))
    }
}

spec fn int_to_string_spec(n: int) -> Seq<char>
    decreases n
{
    if n == 0 { 
        seq!['0'] 
    } else if n < 10 && n > 0 { 
        seq![('0' as int + n) as char]
    } else if n > 0 { 
        int_to_string_spec(n / 10) + seq![('0' as int + (n % 10)) as char]
    } else {
        seq!['0']
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed digit_value function syntax and char conversion */
fn split_string(input: Seq<char>) -> (result: Seq<Seq<char>>)
    ensures
        result == split_string_spec(input),
{
    if input.len() == 0 {
        seq![]
    } else {
        split_helper_impl(input, 0, seq![])
    }
}

fn split_helper_impl(s: Seq<char>, index: int, current: Seq<char>) -> (result: Seq<Seq<char>>)
    requires
        0 <= index <= s.len(),
    ensures
        result == split_helper(s, index, current),
    decreases s.len() - index,
{
    if index >= s.len() {
        if current.len() > 0 { seq![current] } else { seq![] }
    } else if s@[index] == ' ' || s@[index] == '\n' || s@[index] == '\t' {
        if current.len() > 0 { 
            seq![current] + split_helper_impl(s, index + 1, seq![])
        } else { 
            split_helper_impl(s, index + 1, seq![])
        }
    } else {
        split_helper_impl(s, index + 1, current.push(s@[index]))
    }
}

fn is_valid_integer_impl(s: Seq<char>) -> (result: bool)
    ensures
        result == is_valid_integer(s),
{
    if s.len() == 0 {
        false
    } else {
        let mut i: int = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                forall|j: int| 0 <= j < i ==> s@[j] >= '0' && s@[j] <= '9',
        {
            if s@[i] < '0' || s@[i] > '9' {
                return false;
            }
            i = i + 1;
        }
        true
    }
}

fn string_to_int(s: Seq<char>) -> (result: int)
    requires
        is_valid_integer(s),
    ensures
        result == string_to_int_spec(s),
    decreases s.len(),
{
    proof {
        let spec_result = string_to_int_spec(s);
    }
    ghost let digit_value = |c: char| (c as int - '0' as int);
    if s.len() == 1 { 
        digit_value(s@[0])
    } else if s.len() > 1 { 
        let prefix = s.subrange(0, s.len() - 1);
        let last_digit_val = digit_value(s@[s.len() - 1]);
        string_to_int(prefix) * 10 + last_digit_val
    } else {
        0
    }
}

fn int_to_string(n: int) -> (result: Seq<char>)
    requires
        n >= 0,
    ensures
        result == int_to_string_spec(n),
    decreases n,
{
    proof {
        let spec_result = int_to_string_spec(n);
    }
    ghost let char_from_digit = |d: int| ('0' as int + d) as char;
    if n == 0 { 
        seq!['0'] 
    } else if n < 10 { 
        seq![char_from_digit(n)]
    } else { 
        let prefix = int_to_string(n / 10);
        let last_digit = n % 10;
        prefix + seq![char_from_digit(last_digit)]
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires
        valid_input(input@),
    ensures
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        ({
            let parts = split_string_spec(input@);
            let a = string_to_int_spec(parts[0]);
            let b = string_to_int_spec(parts[1]);
            let c = string_to_int_spec(parts[2]);
            let drinks = compute_drinks(a, b, c);
            result@ == int_to_string_spec(drinks) + seq!['\n']
        }),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Using verified helper functions */
{
    let parts = split_string(input@);
    proof {
        assert(parts.len() >= 3);
        assert(is_valid_integer(parts[0]));
        assert(is_valid_integer(parts[1]));
        assert(is_valid_integer(parts[2]));
    }
    
    let a = string_to_int(parts[0]);
    let b = string_to_int(parts[1]);
    let c = string_to_int(parts[2]);
    
    proof {
        assert(1 <= a <= 100);
        assert(1 <= b <= 100);
        assert(1 <= c <= 100);
    }
    
    let quotient = b / a;
    let drinks = if quotient < c { quotient } else { c };
    let drinks_str = int_to_string(drinks) + seq!['\n'];
    
    proof {
        assert(drinks == compute_drinks(a, b, c));
        assert(drinks_str@ == int_to_string_spec(drinks) + seq!['\n']);
        assert(drinks_str@.len() > 0);
        assert(drinks_str@[drinks_str@.len() - 1] == '\n');
    }
    
    drinks_str
}
// </vc-code>


}

fn main() {}