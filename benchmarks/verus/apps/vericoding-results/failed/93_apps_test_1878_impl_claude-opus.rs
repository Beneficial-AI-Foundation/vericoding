// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 0
}

spec fn split_lines_func(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        split_lines_helper(s, 0, 0, seq![])
    }
}

spec fn split_lines_helper(s: Seq<char>, start: int, pos: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases s.len() - pos when pos >= 0 && pos <= s.len()
{
    if pos >= s.len() {
        if start < pos {
            acc.push(s.subrange(start, pos))
        } else {
            acc
        }
    } else if s[pos] == '\n' {
        let new_acc = if start < pos {
            acc.push(s.subrange(start, pos))
        } else {
            acc
        };
        split_lines_helper(s, pos + 1, pos + 1, new_acc)
    } else {
        split_lines_helper(s, start, pos + 1, acc)
    }
}

spec fn parse_int_func(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if s[0] == '-' {
        -parse_int_pos_func(s.subrange(1, s.len() as int))
    } else {
        parse_int_pos_func(s)
    }
}

spec fn parse_int_pos_func(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if '0' <= s[0] && s[0] <= '9' {
        (s[0] as int - '0' as int) + 10 * parse_int_pos_func(s.subrange(1, s.len() as int))
    } else {
        0
    }
}

spec fn parse_ints_func(s: Seq<char>) -> Seq<int> {
    if s.len() == 0 {
        seq![]
    } else {
        parse_ints_helper(s, 0, 0, seq![])
    }
}

spec fn parse_ints_helper(s: Seq<char>, start: int, pos: int, acc: Seq<int>) -> Seq<int>
    decreases s.len() - pos when pos >= 0 && pos <= s.len()
{
    if pos >= s.len() {
        if start < pos {
            acc.push(parse_int_func(s.subrange(start, pos)))
        } else {
            acc
        }
    } else if s[pos] == ' ' {
        let new_acc = if start < pos {
            acc.push(parse_int_func(s.subrange(start, pos)))
        } else {
            acc
        };
        parse_ints_helper(s, pos + 1, pos + 1, new_acc)
    } else {
        parse_ints_helper(s, start, pos + 1, acc)
    }
}

spec fn int_to_string_func(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n > 0 {
        int_to_string_pos(n)
    } else {
        seq!['-'] + int_to_string_pos(-n)
    }
}

spec fn int_to_string_pos(n: int) -> Seq<char>
    decreases n when n > 0
{
    if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string_pos(n / 10) + seq![('0' as int + (n % 10)) as char]
    }
}

spec fn compute_total_area(rectangle_lines: Seq<Seq<char>>) -> int
    decreases rectangle_lines.len()
{
    if rectangle_lines.len() == 0 {
        0
    } else {
        let coords = parse_ints_func(rectangle_lines[0]);
        let area = if coords.len() >= 4 {
            let computed = (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
            if computed >= 0 { computed } else { 0 }
        } else {
            0
        };
        area + compute_total_area(rectangle_lines.subrange(1, rectangle_lines.len() as int))
    }
}

spec fn compute_total_area_partial(rectangle_lines: Seq<Seq<char>>, n: int) -> int
    decreases n when n >= 0
{
    if n <= 0 || rectangle_lines.len() == 0 {
        0
    } else {
        let coords = parse_ints_func(rectangle_lines[0]);
        let area = if coords.len() >= 4 {
            let computed = (coords[2] - coords[0] + 1) * (coords[3] - coords[1] + 1);
            if computed >= 0 { computed } else { 0 }
        } else {
            0
        };
        area + compute_total_area_partial(rectangle_lines.subrange(1, rectangle_lines.len() as int), n - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed integer literal type annotations */

fn parse_int(s: &Vec<char>) -> (n: i64)
    ensures n as int == parse_int_func(s@)
{
    if s.len() == 0 {
        return 0;
    }
    
    let is_negative = s[0] == '-';
    let start_idx = if is_negative { 1 } else { 0 };
    
    let mut result: i64 = 0;
    let mut i: usize = s.len();
    let mut multiplier: i64 = 1;
    
    while i > start_idx
        invariant
            start_idx <= i <= s.len(),
            result >= 0,
            multiplier > 0,
        decreases i
    {
        i = i - 1;
        if s[i] >= '0' && s[i] <= '9' {
            let digit = (s[i] as u8 - '0' as u8) as i64;
            if result <= (i64::MAX - digit) / 10 {
                result = result + digit * multiplier;
                if multiplier <= i64::MAX / 10 {
                    multiplier = multiplier * 10;
                }
            }
        }
    }
    
    if is_negative {
        if result <= i64::MAX {
            -result
        } else {
            i64::MIN
        }
    } else {
        result
    }
}

fn parse_ints(s: &Vec<char>) -> (nums: Vec<i64>)
    ensures nums@.len() >= 0
{
    let mut result: Vec<i64> = Vec::new();
    let mut current_num: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@.len() >= 0,
        decreases s.len() - i
    {
        if s[i] == ' ' {
            if current_num.len() > 0 {
                let n = parse_int(&current_num);
                result.push(n);
                current_num = Vec::new();
            }
        } else {
            current_num.push(s[i]);
        }
        i = i + 1;
    }
    
    if current_num.len() > 0 {
        let n = parse_int(&current_num);
        result.push(n);
    }
    
    result
}

fn int_to_string(n: i64) -> (s: Vec<char>)
    ensures 
        s@.len() >= 1,
        parse_int_func(s@) == n,
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let is_negative = n < 0;
    let mut abs_n: i64 = if is_negative {
        if n == i64::MIN {
            // Handle special case where -n would overflow
            let mut result = Vec::new();
            result.push('-');
            result.push('9');
            result.push('2');
            result.push('2');
            result.push('3');
            result.push('3');
            result.push('7');
            result.push('2');
            result.push('0');
            result.push('3');
            result.push('6');
            result.push('8');
            result.push('5');
            result.push('4');
            result.push('7');
            result.push('7');
            result.push('5');
            result.push('8');
            result.push('0');
            result.push('8');
            return result;
        } else {
            -n
        }
    } else {
        n
    };
    
    let mut digits: Vec<char> = Vec::new();
    
    while abs_n > 0
        invariant
            abs_n >= 0,
            digits@.len() >= 0,
        decreases abs_n
    {
        let digit = (abs_n % 10) as u8;
        digits.push(('0' as u8 + digit) as char);
        abs_n = abs_n / 10;
    }
    
    let mut result: Vec<char> = Vec::new();
    if is_negative {
        result.push('-');
    }
    
    let mut i: usize = digits.len();
    while i > 0
        invariant
            0 <= i <= digits.len(),
            result@.len() >= if is_negative { 1usize } else { 0usize },
        decreases i
    {
        i = i - 1;
        result.push(digits[i]);
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@),
    ensures 
        result@.len() >= 1,
        result@[result@.len() - 1] == '\n',
        exists|total_area: int| {
            &&& total_area >= 0
            &&& result@ == int_to_string_func(total_area) + seq!['\n']
            &&& {
                let processed_input = if input@.len() > 0 && input@[input@.len() - 1] == '\n' {
                    input@
                } else {
                    input@ + seq!['\n']
                };
                let lines = split_lines_func(processed_input);
                if lines.len() == 0 {
                    total_area == 0
                } else {
                    let n = parse_int_func(lines[0]);
                    if n >= 0 && n + 1 <= lines.len() {
                        total_area == compute_total_area(lines.subrange(1, n + 1))
                    } else {
                        total_area == compute_total_area_partial(lines.subrange(1, lines.len() as int), n)
                    }
                }
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow issues and cast operations */
    let mut input_vec = input;
    
    // Ensure input ends with newline
    if input_vec.len() == 0 || input_vec[input_vec.len() - 1] != '\n' {
        input_vec.push('\n');
    }
    
    // Split input into lines
    let mut lines: Vec<Vec<char>> = Vec::new();
    let mut current_line: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < input_vec.len()
        invariant
            0 <= i <= input_vec.len(),
            lines@.len() >= 0,
            current_line@.len() >= 0,
        decreases input_vec.len() - i
    {
        if input_vec[i] == '\n' {
            if current_line.len() > 0 {
                lines.push(current_line);
                current_line = Vec::new();
            }
        } else {
            current_line.push(input_vec[i]);
        }
        i = i + 1;
    }
    
    // Parse the first line to get n
    let n = if lines.len() > 0 {
        parse_int(&lines[0])
    } else {
        0i64
    };
    
    // Compute total area
    let mut total_area: i64 = 0;
    let mut j: usize = 1;
    #[verifier::truncate]
    let limit: usize = if n >= 0 && n <= (lines.len() - 1) as i64 {
        #[verifier::truncate]
        let lim = (n + 1) as usize;
        lim
    } else {
        lines.len()
    };
    
    while j < limit && j < lines.len()
        invariant
            1 <= j <= limit,
            j <= lines.len(),
            total_area >= 0,
        decreases limit - j
    {
        let coords = parse_ints(&lines[j]);
        if coords.len() >= 4 {
            let x1 = coords[0];
            let y1 = coords[1];
            let x2 = coords[2];
            let y2 = coords[3];
            
            if x2 >= x1 && y2 >= y1 {
                let width = x2 - x1 + 1;
                let height = y2 - y1 + 1;
                if width >= 0 && height >= 0 && width <= i64::MAX / height {
                    let area = width * height;
                    if total_area <= i64::MAX - area {
                        total_area = total_area + area;
                    }
                }
            }
        }
        j = j + 1;
    }
    
    // Convert total_area to string
    let result_str = int_to_string(total_area);
    let mut result = Vec::new();
    let mut k: usize = 0;
    while k < result_str.len()
        invariant
            0 <= k <= result_str.len(),
            result@.len() == k as int,
        decreases result_str.len() - k
    {
        result.push(result_str[k]);
        k = k + 1;
    }
    result.push('\n');
    
    result
}
// </vc-code>


}

fn main() {}