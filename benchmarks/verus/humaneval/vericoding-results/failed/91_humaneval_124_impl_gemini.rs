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
/* helper modified by LLM (iteration 4): [Fix compilation error and add is_ascii precondition] */
fn exec_find_hyphen(s: &str, start: usize) -> (res: usize)
    requires
        0 <= start <= s.len(),
        s.is_ascii(),
    ensures
        res == find_first_hyphen(s@, start as int),
{
    let mut i = start;
    while i < s.len()
        invariant
            start <= i <= s.len(),
            s.is_ascii(),
            forall|j: int| start <= j < i ==> s@[j] != '-',
    {
        if s.as_bytes()[i] == b'-' {
            return i;
        }
        i = i + 1;
    }
    s.len()
}

/* helper modified by LLM (iteration 4): [Fix compilation errors using exec code and add is_ascii precondition] */
fn parse_numeric(s: &str) -> (res: Option<u64>)
    requires
        s.is_ascii(),
    ensures
        (is_numeric(s@) && string_to_int(s@) <= u64::MAX) ==> (res.is_some() && res.unwrap() as int == string_to_int(s@)),
        (!is_numeric(s@) || (is_numeric(s@) && string_to_int(s@) > u64::MAX)) ==> res.is_none(),
{
    if s.len() == 0 {
        assert(!is_numeric(s@));
        return None;
    }
    let mut val: u64 = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            s.is_ascii(),
            s.len() > 0,
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> is_digit(s@[j]),
            val as int == string_to_int(s@.subrange(0, i as int)),
    {
        let c = s.as_bytes()[i] as char;
        if !(c >= '0' && c <= '9') {
            proof {
                assert(s@[i] == c);
                assert(!is_digit(s@[i]));
                assert(!is_numeric(s@));
            }
            return None;
        }
        let digit = (c as u64) - ('0' as u64);

        if val > u64::MAX / 10 || (val == u64::MAX / 10 && digit > u64::MAX % 10) {
            return None;
        }
        val = val * 10 + digit;
        
        proof {
            let si = s@.subrange(0, i as int);
            let si1 = s@.subrange(0, i as int + 1);
            assert(string_to_int(si1) == string_to_int(si) * 10 + char_to_int(si1.last()));
        }
        i += 1;
    }
    assert(is_numeric(s@));
    Some(val)
}
// </vc-helpers>

// <vc-spec>
fn valid_date(date: &str) -> (result: bool)
    ensures result == valid_date_format(date@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): [Add ASCII check to satisfy preconditions of helpers.] */
{
    if !date.is_ascii() {
        proof {
            if valid_date_format(date@) {
                assert(date.is_ascii());
            }
        }
        return false;
    }

    // Find first hyphen. Must exist and not be at the beginning.
    let h1 = exec_find_hyphen(date, 0);
    if h1 == 0 || h1 >= date.len() {
        return false;
    }

    // Find second hyphen. Must exist and not be adjacent to the first.
    let h2 = exec_find_hyphen(date, h1 + 1);
    if h2 <= h1 + 1 || h2 >= date.len() {
        return false;
    }

    // Year part must be non-empty
    if h2 + 1 >= date.len() {
        return false;
    }
    
    // There cannot be a third hyphen.
    if exec_find_hyphen(date, h2 + 1) < date.len() {
        return false;
    }
    
    let month_str = &date[..h1];
    let day_str = &date[h1 + 1..h2];
    let year_str = &date[h2 + 1..];
    
    let month_opt = parse_numeric(month_str);
    let day_opt = parse_numeric(day_str);
    let year_opt = parse_numeric(year_str);

    match (month_opt, day_opt, year_opt) {
        (Some(month), Some(day), Some(_year)) => {
            if !(1 <= month && month <= 12) {
                return false;
            }
            if month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12 {
                1 <= day && day <= 31
            } else if month == 4 || month == 6 || month == 9 || month == 11 {
                1 <= day && day <= 30
            } else { // month == 2
                1 <= day && day <= 29
            }
        }
        _ => false, // This covers non-numeric parts
    }
}
// </vc-code>


}

fn main() {}