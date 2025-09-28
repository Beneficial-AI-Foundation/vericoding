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
/* helper modified by LLM (iteration 5): changed to return Vec<String> and build parts from chars */
exec fn split_into_three_parts(s: &str) -> (Vec<String>, bool)
{
    let mut first_hyphen_index = None;
    let mut second_hyphen_index = None;
    let chars: Vec<char> = s.chars().collect();
    let len = chars.len();
    
    // Find the first hyphen
    let mut i = 0;
    while i < len
        invariant 0 <= i <= len
        decreases len - i
    {
        if chars[i] == '-' {
            first_hyphen_index = Some(i);
            break;
        }
        i += 1;
    }
    
    let first_index = if let Some(idx) = first_hyphen_index {
        idx
    } else {
        return (vec![], false);
    };
    
    // Find the second hyphen
    let mut j = first_index + 1;
    while j < len
        invariant first_index + 1 <= j <= len
        decreases len - j
    {
        if chars[j] == '-' {
            second_hyphen_index = Some(j);
            break;
        }
        j += 1;
    }
    
    let second_index = if let Some(idx) = second_hyphen_index {
        idx
    } else {
        return (vec![], false);
    };
    
    // Check that there are exactly three non-empty parts
    if first_index == 0 || second_index == first_index + 1 || second_index == len - 1 {
        return (vec![], false);
    }
    
    // Build the three parts from the chars vector
    let part1: String = chars[0..first_index].iter().cloned().collect();
    let part2: String = chars[(first_index+1)..second_index].iter().cloned().collect();
    let part3: String = chars[(second_index+1)..].iter().cloned().collect();
    
    (vec![part1, part2, part3], true)
}

/* helper modified by LLM (iteration 4): kept from iteration 3, no changes needed */
exec fn is_numeric_str(s: &str) -> bool
{
    if s.is_empty() {
        return false;
    }
    for c in s.chars() {
        if c < '0' || c > '9' {
            return false;
        }
    }
    true
}

/* helper modified by LLM (iteration 4): kept from iteration 3, no changes needed */
exec fn str_to_int(s: &str) -> (result: u64)
    ensures result as int == string_to_int(s@)
{
    let mut res: u64 = 0;
    for c in s.chars() {
        let digit = (c as u32) - ('0' as u32);
        res = res * 10 + (digit as u64);
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn valid_date(date: &str) -> (result: bool)
    ensures result == valid_date_format(date@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): adapted to use String parts and call as_str() */
{
    let (parts, success) = split_into_three_parts(date);
    if !success {
        return false;
    }

    if !is_numeric_str(parts[0].as_str()) || !is_numeric_str(parts[1].as_str()) || !is_numeric_str(parts[2].as_str()) {
        return false;
    }

    let month = str_to_int(parts[0].as_str());
    let day = str_to_int(parts[1].as_str());

    if month < 1 || month > 12 {
        return false;
    }

    if month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12 {
        if day < 1 || day > 31 {
            return false;
        }
    } else if month == 4 || month == 6 || month == 9 || month == 11 {
        if day < 1 || day > 30 {
            return false;
        }
    } else {   // month == 2
        if day < 1 || day > 29 {
            return false;
        }
    }

    true
}
// </vc-code>


}

fn main() {}