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
    let bytes = s.as_bytes();
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count == count_uppercase_in_range(s, 0, i as int),
            bytes == s.as_bytes(),
    {
        let byte_val = bytes[i];
        // Check if the byte value corresponds to an uppercase ASCII letter
        if 65 <= byte_val && byte_val <= 90 {
            count = count + 1;
        }
        i = i + 1;
        
        // Proof assertion to help verification
        assert(count == count_uppercase_in_range(s, 0, i as int)) by {
            // The recursive definition of count_uppercase_in_range should unfold
            // to show that adding the current character maintains the invariant
            assert(s.as_bytes().spec_index((i-1) as int) == byte_val);
            assert(IsUpperCase(byte_val) <==> (65 <= byte_val && byte_val <= 90));
        }
    }
    
    count
}

}