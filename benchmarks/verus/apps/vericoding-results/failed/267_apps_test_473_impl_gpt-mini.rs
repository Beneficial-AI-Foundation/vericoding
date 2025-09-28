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
/* helper modified by LLM (iteration 5): convert byte digit to i32 */
fn byte_to_int_digit(b: u8) -> i32
    requires
        b >= (b'0' as u8) && b <= (b'9' as u8),
    ensures
        result == (b as i32 - (b'0' as u8) as i32),
{
    let result: i32 = (b as i32 - (b'0' as u8) as i32);
    result
}

/* helper modified by LLM (iteration 5): convert two byte digits to i32 */
fn two_byte_digits_to_int(b1: u8, b2: u8) -> i32
    requires
        b1 >= (b'0' as u8) && b1 <= (b'9' as u8),
        b2 >= (b'0' as u8) && b2 <= (b'9' as u8),
    ensures
        result == (b1 as i32 - (b'0' as u8) as i32) * 10 + (b2 as i32 - (b'0' as u8) as i32),
{
    let d1 = byte_to_int_digit(b1);
    let d2 = byte_to_int_digit(b2);
    let result: i32 = d1 * 10 + d2;
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
/* code modified by LLM (iteration 5): parse bytes, compute bedtime, and format result */
{
    let b = stdin_input.as_bytes();
    let n = b.len();

    // find first newline
    let mut i: usize = 0;
    while i < n && b[i] != b'\n'
        invariant
            i <= n,
        decreases n - i
    {
        i = i + 1;
    }
    let first_nl = i;

    // find second newline
    i = i + 1;
    let mut j: usize = i;
    while j < n && b[j] != b'\n'
        invariant
            i <= j && j <= n,
        decreases n - j
    {
        j = j + 1;
    }
    let second_nl = j;

    // parse wake time at positions 0..first_nl
    let wh = two_byte_digits_to_int(b[0], b[1]);
    let wm = two_byte_digits_to_int(b[3], b[4]);

    // parse sleep time at positions first_nl+1 .. second_nl
    let si = first_nl + 1;
    let sh = two_byte_digits_to_int(b[si], b[si + 1]);
    let sm = two_byte_digits_to_int(b[si + 3], b[si + 4]);

    // compute bedtime difference
    let wake_total_min: i32 = wh * 60 + wm;
    let sleep_total_min: i32 = sh * 60 + sm;
    let diff: i32 = wake_total_min - sleep_total_min;
    let bed_total_min: i32 = if diff >= 0 { diff } else { diff + 24 * 60 };
    let bed_hour: i32 = bed_total_min / 60;
    let bed_min: i32 = bed_total_min % 60;

    // format result as "HH:MM\n"
    let result = format!("{:02}:{:02}\n", bed_hour, bed_min);

    proof {
        let s = stdin_input@;
        let fnl = find_first_newline(s);
        let snl = find_second_newline(s, fnl);
        let (ph, pm) = parse_time(s.subrange(0, fnl));
        let (sh_spec, sm_spec) = parse_time(s.subrange(fnl + 1, snl));

        assert(ph == (wh as int));
        assert(pm == (wm as int));
        assert(sh_spec == (sh as int));
        assert(sm_spec == (sm as int));

        let (bh, bm) = calculate_bedtime(ph, pm, sh_spec, sm_spec);
        assert(bh == (bed_hour as int));
        assert(bm == (bed_min as int));

        let r = result@;
        assert(r.len() == 6);
        assert(r[2] == ':');
        assert(r[5] == '\n');
        let rh = (r[0] as int - '0' as int) * 10 + (r[1] as int - '0' as int);
        let rm = (r[3] as int - '0' as int) * 10 + (r[4] as int - '0' as int);
        assert(rh == bh);
        assert(rm == bm);

        assert(valid_output(r));
        assert(correct_bedtime(s, r));
    }

    (result)
}
// </vc-code>


}

fn main() {}