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
proof fn lemma_valid_date_format_implies_three_parts(date: Seq<char>)
    requires
        valid_date_format(date),
    ensures
        split_by_hyphen(date).len() == 3
{
}

proof fn lemma_string_to_int_valid_for_digits(s: Seq<char>)
    requires
        is_numeric(s),
    ensures
        string_to_int(s) >= 0
{
}

proof fn lemma_month_range_valid(month: int)
    requires
        1 <= month <= 12,
    ensures
        month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12 ||
        month == 4 || month == 6 || month == 9 || month == 11 || month == 2
{
}

proof fn lemma_day_range_valid_for_month(month: int, day: int)
    requires
        1 <= month <= 12,
        if month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12 {
            1 <= day <= 31
        } else if month == 4 || month == 6 || month == 9 || month == 11 {
            1 <= day <= 30
        } else {
            1 <= day <= 29
        }
    ensures
        true
{
}
// </vc-helpers>

// <vc-spec>
fn valid_date(date: &str) -> (result: bool)
    ensures result == valid_date_format(date@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed constant type error by using char comparison instead of byte comparison */
{
    let len = date.len();
    
    if len == 0 {
        return false;
    }
    
    let mut hyphen_count = 0;
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            hyphen_count == count_char(date@.subrange(0, i as int), '-'),
    {
        if date.chars().nth(i).unwrap() == '-' {
            hyphen_count += 1;
        }
        i += 1;
    }
    
    if hyphen_count != 2 {
        return false;
    }
    
    let parts: Vec<&str> = date.split('-').collect();
    if parts.len() != 3 {
        return false;
    }
    
    if parts[0].is_empty() || parts[1].is_empty() || parts[2].is_empty() {
        return false;
    }
    
    if !parts[0].chars().all(|c| c.is_ascii_digit()) ||
       !parts[1].chars().all(|c| c.is_ascii_digit()) ||
       !parts[2].chars().all(|c| c.is_ascii_digit()) {
        return false;
    }
    
    let month: u32 = match parts[0].parse() {
        Ok(n) => n,
        Err(_) => return false,
    };
    
    let day: u32 = match parts[1].parse() {
        Ok(n) => n,
        Err(_) => return false,
    };
    
    if !(1 <= month && month <= 12) {
        return false;
    }
    
    let valid_day = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 1 <= day && day <= 31,
        4 | 6 | 9 | 11 => 1 <= day && day <= 30,
        2 => 1 <= day && day <= 29,
        _ => false,
    };
    
    valid_day
}
// </vc-code>


}

fn main() {}