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
/* helper modified by LLM (iteration 5): Corrected return type specification from `(out_h: u8, out_m: u8)` to `(h: u8, m: u8)` for Verus type checking. */
fn parse_time_str(time_str: &[char]) -> (h: u8, m: u8)
    requires
        time_str.len() == 5,
        time_str[2] == ':',
        '0' <= time_str[0] <= '9',
        '0' <= time_str[1] <= '9',
        '0' <= time_str[3] <= '9',
        '0' <= time_str[4] <= '9',
    ensures
        (time_str[0] as int - '0' as int) * 10 + (time_str[1] as int - '0' as int) == h as int,
        (time_str[3] as int - '0' as int) * 10 + (time_str[4] as int - '0' as int) == m as int
{
    let h = (time_str[0] as u8 - b'0') * 10 + (time_str[1] as u8 - b'0');
    let m = (time_str[3] as u8 - b'0') * 10 + (time_str[4] as u8 - b'0');
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
/* code modified by LLM (iteration 5): Fixed type casting issues and added helper for formatted time output to ensure correctness. */
{
    let stdin_input_seq = stdin_input@;

    let mut first_nl_idx: int = -1;
    let mut i: int = 0;
    while i < stdin_input_seq.len()
        invariant
            0 <= i <= stdin_input_seq.len(),
            first_nl_idx == -1 || (0 <= first_nl_idx < i && stdin_input_seq[first_nl_idx] == '\n' &&
                                   (forall|k: int| 0 <= k < first_nl_idx ==> stdin_input_seq[k] != '\n')),
        decreases stdin_input_seq.len() - i
    {
        if stdin_input_seq[i] == '\n' {
            first_nl_idx = i;
            break;
        }
        i = i + 1;
    }
    
    proof {
        assert(exists|j:int| #![trigger find_first_newline(stdin_input_seq)] 0 <= j < stdin_input_seq.len() && stdin_input_seq[j] == '\n');
        assert(first_nl_idx == find_first_newline(stdin_input_seq));
    }
    
    let mut second_nl_idx: int = -1;
    let mut i: int = first_nl_idx + 1;
    while i < stdin_input_seq.len()
        invariant
            first_nl_idx < i <= stdin_input_seq.len(),
            0 <= first_nl_idx,
            second_nl_idx == -1 || (first_nl_idx < second_nl_idx < i && stdin_input_seq[second_nl_idx] == '\n' &&
                                    (forall|k: int| first_nl_idx < k < second_nl_idx ==> stdin_input_seq[k] != '\n')),
        decreases stdin_input_seq.len() - i
    {
        if stdin_input_seq[i] == '\n' {
            second_nl_idx = i;
            break;
        }
        i = i + 1;
    }
    
    proof {
        assert(exists|j: int| #![trigger find_second_newline(stdin_input_seq, first_nl_idx)] first_nl_idx < j < stdin_input_seq.len() && stdin_input_seq[j] == '\n');
        assert(second_nl_idx == find_second_newline(stdin_input_seq, first_nl_idx));
    }

    let wake_time_str_vec = stdin_input_seq.subrange(0, first_nl_idx).to_vec();
    let sleep_time_str_vec = stdin_input_seq.subrange(first_nl_idx + 1, second_nl_idx).to_vec();

    let (wake_h_u8, wake_m_u8) = parse_time_str(&wake_time_str_vec);
    let (sleep_h_u8, sleep_m_u8) = parse_time_str(&sleep_time_str_vec);

    let (wake_h_int, wake_m_int) = (wake_h_u8 as int, wake_m_u8 as int);
    let (sleep_h_int, sleep_m_int) = (sleep_h_u8 as int, sleep_m_u8 as int);
    
    let (bed_h, bed_m) = calculate_bedtime(wake_h_int, wake_m_int, sleep_h_int, sleep_m_int);

    let mut result_string_val = String::new();
    result_string_val.push((b'0' + (bed_h / 10) as u8) as char);
    result_string_val.push((b'0' + (bed_h % 10) as u8) as char);
    result_string_val.push(':');
    result_string_val.push((b'0' + (bed_m / 10) as u8) as char);
    result_string_val.push((b'0' + (bed_m % 10) as u8) as char);
    result_string_val.push('\n');

    proof {
        let s = stdin_input_seq.subrange(0, first_nl_idx);
        let t = stdin_input_seq.subrange(first_nl_idx + 1, second_nl_idx);
        let (wake_hour, wake_min) = parse_time(s);
        let (sleep_hour, sleep_min) = parse_time(t);
        let (expected_bed_hour, expected_bed_min) = calculate_bedtime(wake_hour, wake_min, sleep_hour, sleep_min);

        assert(wake_h_u8 as int == (s@[0] as int - '0' as int) * 10 + (s@[1] as int - '0' as int));
        assert(wake_m_u8 as int == (s@[3] as int - '0' as int) * 10 + (s@[4] as int - '0' as int));
        assert(sleep_h_u8 as int == (t@[0] as int - '0' as int) * 10 + (t@[1] as int - '0' as int));
        assert(sleep_m_u8 as int == (t@[3] as int - '0' as int) * 10 + (t@[4] as int - '0' as int));

        assert(parse_time(s).0 == wake_h_int);
        assert(parse_time(s).1 == wake_m_int);
        assert(parse_time(t).0 == sleep_h_int);
        assert(parse_time(t).1 == sleep_m_int);

        assert(bed_h == expected_bed_hour);
        assert(bed_m == expected_bed_min);
        assert(valid_output(result_string_val@));
        assert(correct_bedtime(stdin_input_seq, result_string_val@));
    }

    result_string_val
}
// </vc-code>


}

fn main() {}