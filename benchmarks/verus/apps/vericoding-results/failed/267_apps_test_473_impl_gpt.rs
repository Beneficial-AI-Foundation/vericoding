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
/* helper modified by LLM (iteration 3): keep simple modulo bounds lemma used in reasoning about time computations */
proof fn lemma_mod_bounds(a: int, m: int)
    requires
        m > 0,
    ensures
        0 <= a % m < m,
{
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
/* code modified by LLM (iteration 3): parse times from input, compute bedtime, and format output without using unsupported byte literals */
{
    let mut it = stdin_input.splitn(3, '\n');
    let s = it.next().unwrap();
    let t = it.next().unwrap();

    let sb = s.as_bytes();
    let tb = t.as_bytes();

    let wh: i32 = (sb[0] as i32 - 48) * 10 + (sb[1] as i32 - 48);
    let wm: i32 = (sb[3] as i32 - 48) * 10 + (sb[4] as i32 - 48);

    let sh: i32 = (tb[0] as i32 - 48) * 10 + (tb[1] as i32 - 48);
    let sm: i32 = (tb[3] as i32 - 48) * 10 + (tb[4] as i32 - 48);

    let wake_total = wh * 60 + wm;
    let sleep_total = sh * 60 + sm;

    let mut diff = wake_total - sleep_total;
    if diff < 0 { diff += 24 * 60; }

    let bh = diff / 60;
    let bm = diff % 60;

    let mut out = String::new();
    let h0 = core::char::from_u32('0' as u32 + (bh / 10) as u32).unwrap();
    let h1 = core::char::from_u32('0' as u32 + (bh % 10) as u32).unwrap();
    let m0 = core::char::from_u32('0' as u32 + (bm / 10) as u32).unwrap();
    let m1 = core::char::from_u32('0' as u32 + (bm % 10) as u32).unwrap();

    out.push(h0);
    out.push(h1);
    out.push(':');
    out.push(m0);
    out.push(m1);
    out.push('\n');

    out
}

// </vc-code>


}

fn main() {}