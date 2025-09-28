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
fn find_newline(s: &str, start_index: usize) -> (result: usize)
    requires
        start_index <= s@.len(),
        exists|i: int| start_index as int <= i < s@.len() && s@[i] == '\n',
    ensures
        start_index as int <= result < s@.len(),
        s@[result] == '\n',
        forall|i: int| start_index as int <= i < result ==> s@[i] != '\n',
{
    let mut i = start_index;
    while i < s.len()
        invariant
            start_index <= i <= s.len(),
            forall|j: int| start_index as int <= j < i ==> s@[j] != '\n',
            exists|k: int| i as int <= k < s@.len() && s@[k] == '\n',
        decreases s.len() - i
    {
        if s.as_bytes()[i] == b'\n' {
            return i;
        }
        i = i + 1;
    }
    unreachable!();
}

/* helper modified by LLM (iteration 4): [removed obsolete lemma call] */
fn parse_time_str(time_str: &str) -> (result: (u8, u8))
    requires
        valid_time_format(time_str@),
    ensures
        result.0 as int == parse_time(time_str@).0,
        result.1 as int == parse_time(time_str@).1,
{
    let bytes = time_str.as_bytes();
    
    let h1 = bytes[0] - b'0';
    let h2 = bytes[1] - b'0';
    let m1 = bytes[3] - b'0';
    let m2 = bytes[4] - b'0';
    
    let h = h1 * 10 + h2;
    let m = m1 * 10 + m2;
    
    (h, m)
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
    /* code modified by LLM (iteration 5): [fixed compilation error by using correct lemma name] */
    // Find the two newline characters that separate the time strings.
    let first_nl_idx = find_newline(stdin_input, 0);
    proof {
        let first_nl = find_first_newline(stdin_input@);
        assert(first_nl_idx as int == first_nl);
        let second_nl = find_second_newline(stdin_input@, first_nl);
        assert(first_nl < second_nl);
        assert(exists|i: int| (first_nl_idx + 1) as int <= i < stdin_input@.len() && stdin_input@[i] == '\n');
    }
    let second_nl_idx = find_newline(stdin_input, first_nl_idx + 1);

    // Extract the two time strings.
    let s_str = stdin_input.substring_view(0, first_nl_idx);
    let t_str = stdin_input.substring_view(first_nl_idx + 1, second_nl_idx);

    // Parse the time strings into hours and minutes.
    let (wake_hour, wake_min) = parse_time_str(s_str);
    let (sleep_hour, sleep_min) = parse_time_str(t_str);

    // Calculate the bedtime in total minutes.
    let wake_total_min = wake_hour as i32 * 60 + wake_min as i32;
    let sleep_total_min = sleep_hour as i32 * 60 + sleep_min as i32;
    let diff = wake_total_min - sleep_total_min;
    let bed_total_min = if diff >= 0 { diff } else { diff + 24 * 60 };
    
    // Convert total minutes back to HH:MM format.
    let bed_hour = bed_total_min / 60;
    let bed_min = bed_total_min % 60;

    proof {
        // Prove that the calculated hours and minutes are within the valid 24-hour range.
        let (s_spec, t_spec) = (s_str@, t_str@);
        let (wh_spec, wm_spec) = parse_time(s_spec);
        let (sh_spec, sm_spec) = parse_time(t_spec);
        let wake_total_min_spec = wh_spec * 60 + wm_spec;
        let sleep_total_min_spec = sh_spec * 60 + sm_spec;
        assert(0 <= wake_total_min_spec < 24 * 60);
        assert(0 <= sleep_total_min_spec < 24 * 60);
        let diff_spec = wake_total_min_spec - sleep_total_min_spec;
        let bed_total_min_spec = if diff_spec >= 0 { diff_spec } else { diff_spec + 24 * 60 };
        assert(0 <= bed_total_min_spec < 24 * 60);
        assert(bed_total_min as int == bed_total_min_spec);
        assert(0 <= bed_hour < 24);
        assert(0 <= bed_min < 60);
    }

    // Format the final output string "HH:MM\n".
    let h1 = (bed_hour / 10) as u8 + b'0';
    let h2 = (bed_hour % 10) as u8 + b'0';
    let m1 = (bed_min / 10) as u8 + b'0';
    let m2 = (bed_min % 10) as u8 + b'0';

    let mut result_bytes: Vec<u8> = Vec::new();
    result_bytes.push(h1);
    result_bytes.push(h2);
    result_bytes.push(b':');
    result_bytes.push(m1);
    result_bytes.push(m2);
    result_bytes.push(b'\n');

    let result = String::from_bytes(result_bytes);
    
    proof {
        vstd::arithmetic::div_mod::lemma_div_mod_is_div_mod(bed_hour as int, 10);
        vstd::arithmetic::div_mod::lemma_div_mod_is_div_mod(bed_min as int, 10);
    }

    result
}
// </vc-code>


}

fn main() {}