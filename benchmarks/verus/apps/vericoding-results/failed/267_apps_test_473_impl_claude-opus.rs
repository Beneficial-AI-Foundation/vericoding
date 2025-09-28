// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_time_format(time_str: Seq<char>) -> bool {
    time_str.len() == 5 &&
    time_str[2] == ':' &&
    '0' <= time_str[0] <= '9' && '0' <= time_str[1] <= '9' &&
    '0' <= time_str[3] <= '9' && '0' <= time_str[4] <= '9' &&
    (time_str[0] as int - '0' as int) * 10 + (time_str[1] as int - '0' as int) <= 23 &&
    (time_str[3] as int - '0' as int) * 10 + (time_str[4] as int - '0' as int) <= 59
}

spec fn find_first_newline(s: Seq<char>) -> int {
    choose|i: int| 0 <= i < s.len() && s[i] == '\n'
}

spec fn find_second_newline(s: Seq<char>, first: int) -> int {
    choose|i: int| first < i < s.len() && s[i] == '\n'
}

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0 &&
    exists|i: int| 0 <= i < stdin_input.len() && stdin_input[i] == '\n' &&
    exists|i: int, j: int| 0 <= i < j < stdin_input.len() && stdin_input[i] == '\n' && stdin_input[j] == '\n' &&
    {
        let first_nl = find_first_newline(stdin_input);
        let second_nl = find_second_newline(stdin_input, first_nl);
        let s = stdin_input.subrange(0, first_nl);
        let t = stdin_input.subrange(first_nl + 1, second_nl);
        valid_time_format(s) && valid_time_format(t)
    }
}

spec fn parse_time(time_str: Seq<char>) -> (int, int) {
    let h = (time_str[0] as int - '0' as int) * 10 + (time_str[1] as int - '0' as int);
    let m = (time_str[3] as int - '0' as int) * 10 + (time_str[4] as int - '0' as int);
    (h, m)
}

spec fn calculate_bedtime(wake_hour: int, wake_min: int, sleep_hour: int, sleep_min: int) -> (int, int) {
    let wake_total_min = wake_hour * 60 + wake_min;
    let sleep_total_min = sleep_hour * 60 + sleep_min;
    let diff = wake_total_min - sleep_total_min;
    let bed_total_min = if diff >= 0 { diff } else { diff + 24 * 60 };
    (bed_total_min / 60, bed_total_min % 60)
}

spec fn valid_output(result: Seq<char>) -> bool {
    result.len() == 6 &&
    result[result.len() - 1] == '\n' &&
    result[2] == ':' &&
    '0' <= result[0] <= '9' && '0' <= result[1] <= '9' &&
    '0' <= result[3] <= '9' && '0' <= result[4] <= '9' &&
    (result[0] as int - '0' as int) * 10 + (result[1] as int - '0' as int) <= 23 &&
    (result[3] as int - '0' as int) * 10 + (result[4] as int - '0' as int) <= 59
}

spec fn correct_bedtime(stdin_input: Seq<char>, result: Seq<char>) -> bool {
    let first_nl = find_first_newline(stdin_input);
    let second_nl = find_second_newline(stdin_input, first_nl);
    let s = stdin_input.subrange(0, first_nl);
    let t = stdin_input.subrange(first_nl + 1, second_nl);
    let (wake_hour, wake_min) = parse_time(s);
    let (sleep_hour, sleep_min) = parse_time(t);
    let (bed_hour, bed_min) = calculate_bedtime(wake_hour, wake_min, sleep_hour, sleep_min);
    let result_hour = (result[0] as int - '0' as int) * 10 + (result[1] as int - '0' as int);
    let result_min = (result[3] as int - '0' as int) * 10 + (result[4] as int - '0' as int);
    result_hour == bed_hour && result_min == bed_min
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires 
        valid_input(stdin_input@),
    ensures 
        valid_output(result@) &&
        correct_bedtime(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use stdin_input@ to get length instead of calling len() on &str */
    let input_chars = stdin_input@;
    let input_len: usize = input_chars.len() as usize;
    
    // Find the newline positions
    let mut first_nl: usize = 0;
    let mut i: usize = 0;
    while i < input_len
        invariant
            0 <= i <= input_len,
            forall|j: int| 0 <= j < i ==> input_chars[j] != '\n' || first_nl == j as usize,
            first_nl < i ==> input_chars[first_nl as int] == '\n',
            first_nl == 0 ==> forall|j: int| 0 <= j < i ==> input_chars[j] != '\n'
    {
        if stdin_input.get_char(i) == '\n' {
            first_nl = i;
            break;
        }
        i = i + 1;
    }
    
    let mut second_nl: usize = first_nl + 1;
    i = first_nl + 1;
    while i < input_len
        invariant
            first_nl < i <= input_len,
            input_chars[first_nl as int] == '\n',
            forall|j: int| first_nl < j < i ==> input_chars[j] != '\n' || second_nl == j as usize,
            second_nl > first_nl,
            second_nl < i ==> input_chars[second_nl as int] == '\n',
            second_nl == first_nl + 1 ==> forall|j: int| first_nl < j < i ==> input_chars[j] != '\n'
    {
        if stdin_input.get_char(i) == '\n' {
            second_nl = i;
            break;
        }
        i = i + 1;
    }
    
    // Extract wake time string
    let wake_time = stdin_input.substring_char(0, first_nl);
    
    // Extract sleep time string  
    let sleep_time = stdin_input.substring_char(first_nl + 1, second_nl);
    
    // Parse wake time
    let wake_h1 = wake_time.get_char(0) as u8 - '0' as u8;
    let wake_h2 = wake_time.get_char(1) as u8 - '0' as u8;
    let wake_hour = wake_h1 as i32 * 10 + wake_h2 as i32;
    
    let wake_m1 = wake_time.get_char(3) as u8 - '0' as u8;
    let wake_m2 = wake_time.get_char(4) as u8 - '0' as u8;
    let wake_min = wake_m1 as i32 * 10 + wake_m2 as i32;
    
    // Parse sleep time
    let sleep_h1 = sleep_time.get_char(0) as u8 - '0' as u8;
    let sleep_h2 = sleep_time.get_char(1) as u8 - '0' as u8;
    let sleep_hour = sleep_h1 as i32 * 10 + sleep_h2 as i32;
    
    let sleep_m1 = sleep_time.get_char(3) as u8 - '0' as u8;
    let sleep_m2 = sleep_time.get_char(4) as u8 - '0' as u8;
    let sleep_min = sleep_m1 as i32 * 10 + sleep_m2 as i32;
    
    // Calculate bedtime
    let wake_total_min = wake_hour * 60 + wake_min;
    let sleep_total_min = sleep_hour * 60 + sleep_min;
    let diff = wake_total_min - sleep_total_min;
    let bed_total_min = if diff >= 0 { diff } else { diff + 24 * 60 };
    let bed_hour = bed_total_min / 60;
    let bed_min = bed_total_min % 60;
    
    // Format output
    let h1 = ((bed_hour / 10) as u8 + '0' as u8) as char;
    let h2 = ((bed_hour % 10) as u8 + '0' as u8) as char;
    let m1 = ((bed_min / 10) as u8 + '0' as u8) as char;
    let m2 = ((bed_min % 10) as u8 + '0' as u8) as char;
    
    let mut result = String::new();
    result.push(h1);
    result.push(h2);
    result.push(':');
    result.push(m1);
    result.push(m2);
    result.push('\n');
    
    result
}
// </vc-code>


}

fn main() {}