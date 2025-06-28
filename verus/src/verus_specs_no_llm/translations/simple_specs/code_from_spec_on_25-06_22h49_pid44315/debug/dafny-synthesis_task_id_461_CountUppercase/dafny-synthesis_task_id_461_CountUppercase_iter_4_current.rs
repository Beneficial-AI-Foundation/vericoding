use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsUpperCase(b: u8) -> bool {
    65 <= b && b <= 90
}

spec fn count_uppercase_in_range(s: &str, start: int, end: int) -> int
    decreases end - start
{
    if start >= end || start < 0 || end > s.len() {
        0
    } else {
        let current_count = if IsUpperCase(s.as_bytes().spec_index(start)) { 1 } else { 0 };
        current_count + count_uppercase_in_range(s, start + 1, end)
    }
}

fn CountUppercase(s: &str) -> (count: usize)
    ensures
        count == count_uppercase_in_range(s, 0, s.len() as int),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count == count_uppercase_in_range(s, 0, i as int),
    {
        let byte_val = s.as_bytes()[i];
        // Check if the byte value corresponds to an uppercase ASCII letter
        if 65 <= byte_val && byte_val <= 90 {
            count = count + 1;
        }
        i = i + 1;
        
        // Proof assertion to help verification
        assert(count == count_uppercase_in_range(s, 0, i as int));
    }
    
    count
}

}