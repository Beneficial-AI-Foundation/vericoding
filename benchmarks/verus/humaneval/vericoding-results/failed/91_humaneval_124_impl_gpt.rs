// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_date_format(date: Seq<char>) -> bool {
    date.len() > 0 &&
    count_char(date, '-') == 2 && {
        let parts = split_by_hyphen(date);
        parts.len() == 3 &&
        parts[0].len() > 0 && parts[1].len() > 0 && parts[2].len() > 0 &&
        is_numeric(parts[0]) && is_numeric(parts[1]) && is_numeric(parts[2]) && {
            let month = string_to_int(parts[0]);
            let day = string_to_int(parts[1]);
            1 <= month <= 12 &&
            if month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12 {
                1 <= day <= 31
            } else if month == 4 || month == 6 || month == 9 || month == 11 {
                1 <= day <= 30
            } else {
                1 <= day <= 29
            }
        }
    }
}

spec fn count_char(s: Seq<char>, c: char) -> nat 
    decreases s.len()
{
    if s.len() == 0 { 
        0
    } else if s[0] == c { 
        1 + count_char(s.subrange(1, s.len() as int), c)
    } else { 
        count_char(s.subrange(1, s.len() as int), c)
    }
}

spec fn is_digit(c: char) -> bool {
    '0' <= c <= '9'
}

spec fn is_numeric(s: Seq<char>) -> bool {
    s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> is_digit(s[i]))
}

spec fn char_to_int(c: char) -> int {
    c as int - '0' as int
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0
    } else if s.len() == 1 { 
        char_to_int(s[0])
    } else { 
        string_to_int(s.subrange(0, s.len() - 1)) * 10 + char_to_int(s[s.len() - 1])
    }
}

spec fn find_first_hyphen(s: Seq<char>, start: int) -> int
    decreases s.len() - start
{
    if start >= s.len() { 
        s.len() as int
    } else if s[start] == '-' { 
        start
    } else { 
        find_first_hyphen(s, start + 1)
    }
}

spec fn split_by_hyphen(s: Seq<char>) -> Seq<Seq<char>> {
    let first_hyphen = find_first_hyphen(s, 0);
    if first_hyphen >= s.len() { 
        seq![s]
    } else {
        let second_hyphen = find_first_hyphen(s, first_hyphen + 1);
        if second_hyphen >= s.len() { 
            seq![s.subrange(0, first_hyphen), s.subrange(first_hyphen + 1, s.len() as int)]
        } else { 
            seq![s.subrange(0, first_hyphen), s.subrange(first_hyphen + 1, second_hyphen), s.subrange(second_hyphen + 1, s.len() as int)]
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): executable helpers for numeric checks and day bounds */
fn is_numeric_bytes(s: &str) -> (r: bool) {
    let bytes = s.as_bytes();
    let n = bytes.len();
    if n == 0 { return false; }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
        decreases n - i
    {
        let b = bytes[i];
        if !(b'0' <= b && b <= b'9') {
            return false;
        }
        i += 1;
    }
    true
}

/* helper modified by LLM (iteration 2): check if month string is in range 1..12 without parsing */
fn month_in_1_to_12(s: &str) -> (r: bool) {
    let bytes = s.as_bytes();
    let n = bytes.len();
    if n == 0 { return false; }
    if !is_numeric_bytes(s) { return false; }
    if n >= 3 { return false; }
    if n == 1 {
        let d = bytes[0];
        return d >= b'1' && d <= b'9';
    } else {
        let d1 = bytes[0];
        let d2 = bytes[1];
        if d1 == b'0' {
            return d2 >= b'1' && d2 <= b'9';
        } else if d1 == b'1' {
            return d2 <= b'2';
        } else {
            return false;
        }
    }
}

/* helper modified by LLM (iteration 2): check if day string is within an upper bound (29/30/31) */
fn day_leq_max(s: &str, max: u8) -> (r: bool) {
    let bytes = s.as_bytes();
    let n = bytes.len();
    if n == 0 { return false; }
    if !is_numeric_bytes(s) { return false; }
    if n >= 3 { return false; }
    if n == 1 {
        let d = bytes[0];
        return d >= b'1' && d <= b'9';
    }
    let d1 = bytes[0];
    let d2 = bytes[1];
    if d1 == b'0' {
        return d2 >= b'1' && d2 <= b'9';
    } else if d1 == b'1' || d1 == b'2' {
        if max >= 29 { return d2 >= b'0' && d2 <= b'9'; } else { return false; }
    } else if d1 == b'3' {
        if max >= 31 {
            return d2 == b'0' || d2 == b'1';
        } else if max >= 30 {
            return d2 == b'0';
        } else {
            return false;
        }
    } else {
        return false;
    }
}
// </vc-helpers>

// <vc-spec>
fn valid_date(date: &str) -> (result: bool)
    ensures result == valid_date_format(date@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement executable date validation logic without calling spec functions */
    let n = date.len();
    if n == 0 { return false; }

    let bytes = date.as_bytes();
    let mut i: usize = 0;
    let mut hyphens: usize = 0;
    let mut first: usize = 0;
    let mut second: usize = 0;

    while i < n
        invariant
            i <= n,
            hyphens <= 2,
        decreases n - i
    {
        if bytes[i] == b'-' {
            if hyphens == 0 {
                first = i;
            } else if hyphens == 1 {
                second = i;
            }
            hyphens += 1;
        }
        i += 1;
    }

    if hyphens != 2 { return false; }
    if first == 0 { return false; }
    if second == first + 1 { return false; }
    if second + 1 >= n { return false; }

    let p0 = &date[0..first];
    let p1 = &date[first + 1..second];
    let p2 = &date[second + 1..n];

    if !(is_numeric_bytes(p0) && is_numeric_bytes(p1) && is_numeric_bytes(p2)) {
        return false;
    }
    if !month_in_1_to_12(p0) { return false; }

    // Determine max day based on month without parsing
    let bytes0 = p0.as_bytes();
    let max_day: u8;
    if bytes0.len() == 1 {
        let m = bytes0[0];
        if m == b'4' || m == b'6' || m == b'9' {
            max_day = 30;
        } else if m == b'2' {
            max_day = 29;
        } else {
            max_day = 31;
        }
    } else {
        // months 10..12
        let m2 = bytes0[1];
        if m2 == b'0' {
            max_day = 31; // October
        } else if m2 == b'1' {
            max_day = 30; // November
        } else {
            max_day = 31; // December
        }
    }

    if max_day == 31 {
        return day_leq_max(p1, 31);
    } else if max_day == 30 {
        return day_leq_max(p1, 30);
    } else {
        return day_leq_max(p1, 29);
    }
}
// </vc-code>


}

fn main() {}