use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
}

spec fn count_digits_in_range(s: String, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        let current_count = if IsDigit(s.spec_index(start)) { 1 } else { 0 };
        current_count + count_digits_in_range(s, start + 1, end)
    }
}

fn CountDigits(s: String) -> (count: int)
    ensures
        count >= 0,
        count == count_digits_in_range(s, 0, s.len() as int),
{
    let mut count = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count >= 0,
            count == count_digits_in_range(s, 0, i as int),
    {
        if IsDigit(s.spec_index(i as int)) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}