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

// </vc-helpers>

// <vc-spec>
fn valid_date(date: &str) -> (result: bool)
    ensures result == valid_date_format(date@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix len() call on &str by using @.len() */
    if date@.len() == 0 {
        return false;
    }
    
    let mut hyphen_count: usize = 0;
    let mut first_hyphen: usize = 0;
    let mut second_hyphen: usize = 0;
    let mut i: usize = 0;
    
    while i < date@.len()
        invariant
            0 <= i <= date@.len(),
            hyphen_count <= 2,
            hyphen_count as nat == count_char(date@.subrange(0, i as int), '-'),
            hyphen_count >= 1 ==> first_hyphen < i,
            hyphen_count >= 1 ==> date@[first_hyphen as int] == '-',
            hyphen_count >= 1 ==> first_hyphen as int == find_first_hyphen(date@, 0),
            hyphen_count >= 2 ==> second_hyphen < i,
            hyphen_count >= 2 ==> second_hyphen > first_hyphen,
            hyphen_count >= 2 ==> date@[second_hyphen as int] == '-',
            hyphen_count >= 2 ==> second_hyphen as int == find_first_hyphen(date@, first_hyphen as int + 1),
    {
        if date@[i as int] == '-' {
            if hyphen_count == 0 {
                first_hyphen = i;
            } else if hyphen_count == 1 {
                second_hyphen = i;
            }
            hyphen_count = hyphen_count + 1;
            if hyphen_count > 2 {
                return false;
            }
        }
        i = i + 1;
    }
    
    if hyphen_count != 2 {
        return false;
    }
    
    if first_hyphen == 0 || second_hyphen == first_hyphen + 1 || second_hyphen == date@.len() - 1 {
        return false;
    }
    
    let mut month: u32 = 0;
    let mut day: u32 = 0;
    
    i = 0;
    while i < first_hyphen
        invariant
            0 <= i <= first_hyphen,
            first_hyphen < date@.len(),
            month <= 999,
            month as int == string_to_int(date@.subrange(0, i as int)),
            forall|j: int| 0 <= j < i ==> is_digit(date@[j]),
    {
        let c = date@[i as int];
        if c < '0' || c > '9' {
            return false;
        }
        month = month * 10 + (c as u32 - '0' as u32);
        i = i + 1;
    }
    
    i = first_hyphen + 1;
    while i < second_hyphen
        invariant
            first_hyphen + 1 <= i <= second_hyphen,
            second_hyphen < date@.len(),
            day <= 999,
            day as int == string_to_int(date@.subrange(first_hyphen as int + 1, i as int)),
            forall|j: int| first_hyphen as int + 1 <= j < i ==> is_digit(date@[j]),
    {
        let c = date@[i as int];
        if c < '0' || c > '9' {
            return false;
        }
        day = day * 10 + (c as u32 - '0' as u32);
        i = i + 1;
    }
    
    i = second_hyphen + 1;
    while i < date@.len()
        invariant
            second_hyphen + 1 <= i <= date@.len(),
            forall|j: int| second_hyphen as int + 1 <= j < i ==> is_digit(date@[j]),
    {
        let c = date@[i as int];
        if c < '0' || c > '9' {
            return false;
        }
        i = i + 1;
    }
    
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