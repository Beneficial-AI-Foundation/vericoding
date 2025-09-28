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
/* helper modified by LLM (iteration 5): fixed ghost code usage in executable functions */
fn count_char_exec(s: &str, c: char) -> (result: usize)
    requires s@.len() < usize::MAX
    ensures result == count_char(s@, c)
{
    let mut count = 0;
    let mut i = 0usize;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            count == count_char(s@.subrange(0, i as int), c),
        decreases s@.len() - i
    {
        if s.chars().nth(i).unwrap() == c {
            count += 1;
        }
        i += 1;
    }
    count
}

fn is_digit_exec(c: char) -> (result: bool)
    ensures result == is_digit(c)
{
    '0' <= c && c <= '9'
}

fn is_numeric_exec(s: &str) -> (result: bool)
    ensures result == is_numeric(s@)
{
    if s.len() == 0 {
        return false;
    }
    for c in s.chars() {
        if !is_digit_exec(c) {
            return false;
        }
    }
    true
}

fn char_to_int_exec(c: char) -> (result: usize)
    requires is_digit(c)
    ensures result == char_to_int(c)
{
    (c as u8 - ('0' as u8)) as usize
}

fn string_to_int_exec(s: &str) -> (result: usize)
    requires is_numeric(s@), s@.len() > 0
    ensures result == string_to_int(s@)
{
    let mut result = 0;
    for c in s.chars() {
        result = result * 10 + char_to_int_exec(c);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn valid_date(date: &str) -> (result: bool)
    ensures result == valid_date_format(date@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed ghost code usage in executable context */
    if date.len() == 0 {
        return false;
    }
    
    let hyphen_count = count_char_exec(date, '-');
    if hyphen_count != 2 {
        return false;
    }
    
    let parts: Vec<&str> = date.split('-').collect();
    if parts.len() != 3 {
        return false;
    }
    
    if parts[0].len() == 0 || parts[1].len() == 0 || parts[2].len() == 0 {
        return false;
    }
    
    if !is_numeric_exec(parts[0]) || !is_numeric_exec(parts[1]) || !is_numeric_exec(parts[2]) {
        return false;
    }
    
    let month = string_to_int_exec(parts[0]);
    let day = string_to_int_exec(parts[1]);
    
    if month < 1 || month > 12 {
        return false;
    }
    
    if month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12 {
        1 <= day && day <= 31
    } else if month == 4 || month == 6 || month == 9 || month == 11 {
        1 <= day && day <= 30
    } else {
        1 <= day && day <= 29
    }
}
// </vc-code>


}

fn main() {}