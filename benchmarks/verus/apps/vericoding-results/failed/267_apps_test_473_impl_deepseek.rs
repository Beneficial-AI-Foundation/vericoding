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

proof fn lemma_time_format_to_digits(time_str: Seq<char>)
    requires
        valid_time_format(time_str),
    ensures
        (time_str[0] as int - '0' as int) * 10 + (time_str[1] as int - '0' as int) <= 23,
        (time_str[3] as int - '0' as int) * 10 + (time_str[4] as int - '0' as int) <= 59
{
}

fn parse_time_impl(time_str: &str) -> (result: (u8, u8))
    requires
        valid_time_format(time_str@),
    ensures
        result.0 == (time_str@[0] as int - '0' as int) * 10 + (time_str@[1] as int - '0' as int) as u8,
        result.1 == (time_str@[3] as int - '0' as int) * 10 + (time_str@[4] as int - '0' as int) as u8,
        result.0 <= 23,
        result.1 <= 59
{
    proof { lemma_time_format_to_digits(time_str@); }
    
    let chars: Vec<char> = time_str.chars().collect();
    let h1 = (chars[0] as u32 - '0' as u32) as u8;
    let h2 = (chars[1] as u32 - '0' as u32) as u8;
    let m1 = (chars[3] as u32 - '0' as u32) as u8;
    let m2 = (chars[4] as u32 - '0' as u32) as u8;
    
    let hour = h1 * 10 + h2;
    let min = m1 * 10 + m2;
    
    (hour, min)
}

fn format_time(hour: u8, min: u8) -> (result: String)
    requires
        0 <= hour <= 23,
        0 <= min <= 59,
    ensures
        valid_output(result@),
        (result@[0] as int - '0' as int) * 10 + (result@[1] as int - '0' as int) == hour as int,
        (result@[3] as int - '0' as int) * 10 + (result@[4] as int - '0' as int) == min as int
{
    let h1: u8 = (hour / 10) as u8;
    let h2: u8 = (hour % 10) as u8;
    let m1: u8 = (min / 10) as u8;
    let m2: u8 = (min % 10) as u8;
    
    let mut result = String::new();
    result.push((h1 + b'0') as char);
    result.push((h2 + b'0') as char);
    result.push(':');
    result.push((m1 + b'0') as char);
    result.push((m2 + b'0') as char);
    result.push('\n');
    result
}

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
    /* code modified by LLM (iteration 5): Fix integer casting to use ghost variables */
    let first_nl = stdin_input.find('\n').unwrap();
    let wake_time_str = &stdin_input[0..first_nl];
    
    let remaining = &stdin_input[first_nl + 1..];
    let second_nl = remaining.find('\n').unwrap();
    let sleep_time_str = &remaining[0..second_nl];
    
    let (wake_hour, wake_min) = parse_time_impl(wake_time_str);
    let (sleep_hour, sleep_min) = parse_time_impl(sleep_time_str);
    
    proof {
        let wake_total_min = (wake_hour as int) * 60 + (wake_min as int);
        let sleep_total_min = (sleep_hour as int) * 60 + (sleep_min as int);
        let diff = wake_total_min - sleep_total_min;
        let bed_total_min = if diff >= 0 { diff } else { diff + 24 * 60 };
        let bed_hour = (bed_total_min / 60) as u8;
        let bed_min = (bed_total_min % 60) as u8;
        assert(bed_hour <= 23 && bed_min <= 59);
    }
    
    let wake_total_min_i32: i32 = (wake_hour as i32) * 60 + (wake_min as i32);
    let sleep_total_min_i32: i32 = (sleep_hour as i32) * 60 + (sleep_min as i32);
    
    let diff = wake_total_min_i32 - sleep_total_min_i32;
    let bed_total_min = if diff >= 0 { diff } else { diff + 24 * 60 };
    
    let bed_hour = (bed_total_min / 60) as u8;
    let bed_min = (bed_total_min % 60) as u8;
    
    format_time(bed_hour, bed_min)
}
// </vc-code>


}

fn main() {}