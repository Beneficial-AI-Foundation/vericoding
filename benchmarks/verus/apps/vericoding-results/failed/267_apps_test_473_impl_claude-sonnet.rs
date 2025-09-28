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
/* helper modified by LLM (iteration 5): Fixed char access by converting string to Vec<char> and removed slice operations */
fn char_to_digit(c: char) -> (result: u8)
    requires
        '0' <= c <= '9',
    ensures
        result == c as u8 - '0' as u8,
        result <= 9,
{
    (c as u8) - ('0' as u8)
}

fn digit_to_char(d: u8) -> (result: char)
    requires
        d <= 9,
    ensures
        result as u8 - '0' as u8 == d,
        '0' <= result <= '9',
{
    ((d + ('0' as u8)) as char)
}

fn find_newline_index(s: &str, start: usize) -> (result: usize)
    requires
        start < s@.len(),
        exists|i: int| start <= i < s@.len() && s@[i] == '\n',
    ensures
        start <= result < s@.len(),
        s@[result as int] == '\n',
        forall|i: int| start <= i < result ==> s@[i] != '\n',
{
    let chars: Vec<char> = s.chars().collect();
    let mut i = start;
    while i < chars.len()
        invariant
            start <= i <= s@.len(),
            forall|j: int| start <= j < i ==> s@[j] != '\n',
            exists|k: int| i <= k < s@.len() && s@[k] == '\n',
            chars@.len() == s@.len(),
            forall|j: int| 0 <= j < s@.len() ==> chars@[j] == s@[j],
    {
        if chars[i] == '\n' {
            return i;
        }
        i += 1;
    }
    unreached()
}

fn parse_time_from_str(time_str: &str) -> (result: (u8, u8))
    requires
        valid_time_format(time_str@),
    ensures
        result.0 as int == (time_str@[0] as int - '0' as int) * 10 + (time_str@[1] as int - '0' as int),
        result.1 as int == (time_str@[3] as int - '0' as int) * 10 + (time_str@[4] as int - '0' as int),
{
    let chars: Vec<char> = time_str.chars().collect();
    let h1 = char_to_digit(chars[0]);
    let h2 = char_to_digit(chars[1]);
    let m1 = char_to_digit(chars[3]);
    let m2 = char_to_digit(chars[4]);
    let hour = h1 * 10 + h2;
    let min = m1 * 10 + m2;
    (hour, min)
}

fn format_time(hour: u8, min: u8) -> (result: String)
    requires
        hour <= 23,
        min <= 59,
    ensures
        valid_output(result@),
        (result@[0] as int - '0' as int) * 10 + (result@[1] as int - '0' as int) == hour as int,
        (result@[3] as int - '0' as int) * 10 + (result@[4] as int - '0' as int) == min as int,
{
    let h1 = digit_to_char(hour / 10);
    let h2 = digit_to_char(hour % 10);
    let m1 = digit_to_char(min / 10);
    let m2 = digit_to_char(min % 10);
    let mut result = String::new();
    result.push(h1);
    result.push(h2);
    result.push(':');
    result.push(m1);
    result.push(m2);
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
    /* code modified by LLM (iteration 5): Fixed slice operations by using individual char access */
    let chars: Vec<char> = stdin_input.chars().collect();
    
    let first_nl = find_newline_index(stdin_input, 0);
    let second_nl = find_newline_index(stdin_input, first_nl + 1);
    
    let mut wake_chars: Vec<char> = Vec::new();
    let mut i = 0;
    while i < first_nl
        invariant
            0 <= i <= first_nl,
            wake_chars@.len() == i,
            forall|j: int| 0 <= j < i ==> wake_chars@[j] == chars@[j],
    {
        wake_chars.push(chars[i]);
        i += 1;
    }
    
    let mut sleep_chars: Vec<char> = Vec::new();
    let mut j = first_nl + 1;
    while j < second_nl
        invariant
            first_nl + 1 <= j <= second_nl,
            sleep_chars@.len() == j - first_nl - 1,
            forall|k: int| 0 <= k < j - first_nl - 1 ==> sleep_chars@[k] == chars@[first_nl + 1 + k],
    {
        sleep_chars.push(chars[j]);
        j += 1;
    }
    
    let wake_time_str: String = wake_chars.iter().collect();
    let sleep_time_str: String = sleep_chars.iter().collect();
    
    let (wake_hour, wake_min) = parse_time_from_str(&wake_time_str);
    let (sleep_hour, sleep_min) = parse_time_from_str(&sleep_time_str);
    
    let wake_total_min = wake_hour as u16 * 60 + wake_min as u16;
    let sleep_total_min = sleep_hour as u16 * 60 + sleep_min as u16;
    let diff = wake_total_min as i16 - sleep_total_min as i16;
    let bed_total_min = if diff >= 0 { diff as u16 } else { (diff + 24 * 60) as u16 };
    let bed_hour = (bed_total_min / 60) as u8;
    let bed_min = (bed_total_min % 60) as u8;
    
    format_time(bed_hour, bed_min)
}
// </vc-code>


}

fn main() {}