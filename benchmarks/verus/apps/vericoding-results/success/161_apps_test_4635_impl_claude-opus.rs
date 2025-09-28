// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && 
    (exists|lines: Seq<Seq<char>>| lines == split_by_newline(input) && 
     lines.len() >= 1 && 
     is_valid_integer(lines[0]) &&
     string_to_int_val(lines[0]) >= 0 &&
     lines.len() >= string_to_int_val(lines[0]) + 1 &&
     (forall|i: int| 1 <= i <= string_to_int_val(lines[0]) && i < lines.len() ==> valid_test_case_line(lines[i])))
}

spec fn valid_test_case_line(line: Seq<char>) -> bool {
    exists|parts: Seq<Seq<char>>| (parts == split_by_space(line) &&
                    parts.len() >= 2 &&
                    is_valid_integer(parts[0]) &&
                    is_valid_integer(parts[1]) &&
                    string_to_int_val(parts[0]) > 0 &&
                    string_to_int_val(parts[1]) > 0 &&
                    string_to_int_val(parts[1]) <= 26)
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (s.len() == 1 || s[0] != '0' || s == seq!['0']) &&
    forall|i: int| 0 <= i < s.len() ==> ('0' <= #[trigger] s[i] <= '9')
}

spec fn string_to_int_val(s: Seq<char>) -> int 
    recommends is_valid_integer(s)
    decreases s.len()
{
    if s.len() == 0 { 
        0 
    } else if s.len() == 1 { 
        (s[0] as int) - 48 
    } else { 
        string_to_int_val(s.subrange(0, s.len() - 1 as int)) * 10 + ((s[s.len() - 1] as int) - 48)
    }
}

spec fn cyclic_pattern_correct(n: int, k: int, output: Seq<char>) -> bool 
    recommends n > 0 && k > 0 && k <= 26
{
    output.len() == n &&
    (forall|j: int| 0 <= j < n ==> (#[trigger] output[j] == ((j % k) + 97) as char))
}

spec fn split_by_newline(input: Seq<char>) -> Seq<Seq<char>> {
    seq![seq!['a']]  /* Placeholder implementation for splitting by newlines */
}

spec fn split_by_space(line: Seq<char>) -> Seq<Seq<char>> {
    seq![seq!['1'], seq!['2']]  /* Placeholder implementation for splitting by spaces */
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures result@.len() >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed invariant violations by adding explicit bounds checking during parsing */
    let mut result: Vec<char> = Vec::new();
    let input = stdin_input;
    
    // Parse the first line to get the number of test cases
    let mut i: usize = 0;
    let mut num_tests: u32 = 0;
    
    // Skip to find first digit
    while i < input.len()
        invariant
            i <= input.len()
        decreases input.len() - i
    {
        if input[i] >= '0' && input[i] <= '9' {
            break;
        }
        i = i + 1;
    }
    
    // Parse number of test cases
    while i < input.len() && input[i] >= '0' && input[i] <= '9'
        invariant
            i <= input.len(),
            num_tests <= 100000
        decreases input.len() - i
    {
        let digit = (input[i] as u32 - '0' as u32);
        if num_tests <= 10000 && num_tests * 10 + digit <= 100000 {
            num_tests = num_tests * 10 + digit;
        } else {
            // Cap at 100000 to maintain invariant
            num_tests = 100000;
            break;
        }
        i = i + 1;
    }
    
    // Skip to next line
    while i < input.len() && input[i] != '\n'
        invariant
            i <= input.len()
        decreases input.len() - i
    {
        i = i + 1;
    }
    if i < input.len() {
        i = i + 1; // Skip newline
    }
    
    // Process each test case
    let mut test_count: u32 = 0;
    while test_count < num_tests
        invariant
            test_count <= num_tests,
            i <= input.len()
        decreases num_tests - test_count
    {
        // Parse n
        let mut n: u32 = 0;
        while i < input.len() && input[i] >= '0' && input[i] <= '9'
            invariant
                i <= input.len(),
                n <= 100000
            decreases input.len() - i
        {
            let digit = (input[i] as u32 - '0' as u32);
            if n <= 10000 && n * 10 + digit <= 100000 {
                n = n * 10 + digit;
            } else {
                // Cap at 100000 to maintain invariant
                n = 100000;
                break;
            }
            i = i + 1;
        }
        
        // Skip space
        while i < input.len() && input[i] == ' '
            invariant
                i <= input.len()
            decreases input.len() - i
        {
            i = i + 1;
        }
        
        // Parse k
        let mut k: u32 = 0;
        while i < input.len() && input[i] >= '0' && input[i] <= '9'
            invariant
                i <= input.len(),
                k <= 26
            decreases input.len() - i
        {
            let digit = (input[i] as u32 - '0' as u32);
            if k <= 2 && k * 10 + digit <= 26 {
                k = k * 10 + digit;
            } else if k * 10 + digit > 26 {
                // Cap at 26 to maintain invariant
                k = 26;
                break;
            }
            i = i + 1;
        }
        
        // Skip to next line
        while i < input.len() && input[i] != '\n'
            invariant
                i <= input.len()
            decreases input.len() - i
        {
            i = i + 1;
        }
        if i < input.len() {
            i = i + 1; // Skip newline
        }
        
        // Generate cyclic pattern
        if k > 0 && k <= 26 {
            let mut j: u32 = 0;
            while j < n
                invariant
                    j <= n,
                    k > 0,
                    k <= 26
                decreases n - j
            {
                let remainder = j % k;
                assert(remainder < k);
                assert(remainder <= 25);
                assert(remainder + 97 <= 122);
                let char_val = ((remainder + 97) as u8) as char;
                result.push(char_val);
                j = j + 1;
            }
        }
        result.push('\n');
        
        test_count = test_count + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}