// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() == 5 && input.subrange(0, 4).len() == 4 &&
    (forall|i: int| 0 <= i < 4 ==> ('0' <= #[trigger] input[i] <= '9')) &&
    input[4] == '\n'
}

spec fn char_to_digit(c: char) -> int {
    (c as int) - ('0' as int)
}

spec fn evaluate_expression(a: int, b: int, c: int, d: int, op1: char, op2: char, op3: char) -> int {
    let b_val = if op1 == '+' { b } else { -b };
    let c_val = if op2 == '+' { c } else { -c };
    let d_val = if op3 == '+' { d } else { -d };
    a + b_val + c_val + d_val
}

spec fn solution_exists(input: Seq<char>) -> bool {
    &&& valid_input(input)
    &&& {
        let a = char_to_digit(input[0]);
        let b = char_to_digit(input[1]);
        let c = char_to_digit(input[2]);
        let d = char_to_digit(input[3]);
        exists|op1: char, op2: char, op3: char| 
            (op1 == '+' || op1 == '-') &&
            (op2 == '+' || op2 == '-') &&
            (op3 == '+' || op3 == '-') &&
            evaluate_expression(a, b, c, d, op1, op2, op3) == 7
    }
}

spec fn valid_output(result: Seq<char>, input: Seq<char>) -> bool {
    &&& valid_input(input)
    &&& result.len() == 10 
    &&& result.subrange(7, 9) =~= seq!['=', '7']
    &&& result[9] == '\n'
    &&& result[0] == input[0] && result[2] == input[1] 
    &&& result[4] == input[2] && result[6] == input[3]
    &&& (result[1] == '+' || result[1] == '-')
    &&& (result[3] == '+' || result[3] == '-')
    &&& (result[5] == '+' || result[5] == '-')
    &&& {
        let a = char_to_digit(input[0]);
        let b = char_to_digit(input[1]);
        let c = char_to_digit(input[2]);
        let d = char_to_digit(input[3]);
        evaluate_expression(a, b, c, d, result[1], result[3], result[5]) == 7
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(input@),
        solution_exists(input@),
    ensures valid_output(result@, input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed int usage in exec mode by using i32 */
    let a = input[0];
    let b = input[1];
    let c = input[2];
    let d = input[3];
    
    let a_val = (a as u32 - '0' as u32) as i32;
    let b_val = (b as u32 - '0' as u32) as i32;
    let c_val = (c as u32 - '0' as u32) as i32;
    let d_val = (d as u32 - '0' as u32) as i32;
    
    let mut op1: char = '+';
    let mut op2: char = '+';
    let mut op3: char = '+';
    
    if a_val + b_val + c_val + d_val == 7 {
        op1 = '+';
        op2 = '+';
        op3 = '+';
    } else if a_val + b_val + c_val - d_val == 7 {
        op1 = '+';
        op2 = '+';
        op3 = '-';
    } else if a_val + b_val - c_val + d_val == 7 {
        op1 = '+';
        op2 = '-';
        op3 = '+';
    } else if a_val + b_val - c_val - d_val == 7 {
        op1 = '+';
        op2 = '-';
        op3 = '-';
    } else if a_val - b_val + c_val + d_val == 7 {
        op1 = '-';
        op2 = '+';
        op3 = '+';
    } else if a_val - b_val + c_val - d_val == 7 {
        op1 = '-';
        op2 = '+';
        op3 = '-';
    } else if a_val - b_val - c_val + d_val == 7 {
        op1 = '-';
        op2 = '-';
        op3 = '+';
    } else {
        op1 = '-';
        op2 = '-';
        op3 = '-';
    }
    
    let result = vec![a, op1, b, op2, c, op3, d, '=', '7', '\n'];
    
    proof {
        assert(result@.len() == 10);
        assert(result@[0] == input@[0]);
        assert(result@[2] == input@[1]);
        assert(result@[4] == input@[2]);
        assert(result@[6] == input@[3]);
        assert(result@[7] == '=');
        assert(result@[8] == '7');
        assert(result@[9] == '\n');
        assert(op1 == '+' || op1 == '-');
        assert(op2 == '+' || op2 == '-');
        assert(op3 == '+' || op3 == '-');
        assert(char_to_digit(a) == a_val as int);
        assert(char_to_digit(b) == b_val as int);
        assert(char_to_digit(c) == c_val as int);
        assert(char_to_digit(d) == d_val as int);
        assert(evaluate_expression(a_val as int, b_val as int, c_val as int, d_val as int, op1, op2, op3) == 7);
    }
    
    result
}
// </vc-code>


}

fn main() {}