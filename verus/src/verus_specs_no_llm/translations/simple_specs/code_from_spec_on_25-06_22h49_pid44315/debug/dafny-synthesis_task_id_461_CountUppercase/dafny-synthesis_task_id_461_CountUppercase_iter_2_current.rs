use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsUpperCase(c: char) -> bool {
    65 <= c as int && c as int <= 90
}

spec fn count_uppercase_in_range(s: &str, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        let current_count = if IsUpperCase(s.spec_index(start)) { 1 } else { 0 };
        current_count + count_uppercase_in_range(s, start + 1, end)
    }
}

fn CountUppercase(s: &str) -> (count: usize)
    ensures
        count >= 0,
        count == count_uppercase_in_range(s, 0, s.len() as int),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count >= 0,
            count == count_uppercase_in_range(s, 0, i as int),
    {
        let c = s.as_bytes()[i] as char;
        if IsUpperCase(c) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}