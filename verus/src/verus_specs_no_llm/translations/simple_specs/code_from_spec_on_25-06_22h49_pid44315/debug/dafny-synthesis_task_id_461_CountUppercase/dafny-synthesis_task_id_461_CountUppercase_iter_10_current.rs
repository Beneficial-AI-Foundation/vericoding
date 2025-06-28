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

proof fn lemma_count_uppercase_append(s: &str, start: int, mid: int, end: int)
    requires
        0 <= start <= mid <= end <= s.len(),
    ensures
        count_uppercase_in_range(s, start, end) == 
        count_uppercase_in_range(s, start, mid) + count_uppercase_in_range(s, mid, end),
    decreases end - start
{
    if start >= mid {
        // Base case: start == mid
        assert(count_uppercase_in_range(s, start, mid) == 0);
        assert(count_uppercase_in_range(s, start, end) == count_uppercase_in_range(s, mid, end));
    } else {
        // Recursive case
        lemma_count_uppercase_append(s, start + 1, mid, end);
        
        // Expand the definitions
        assert(count_uppercase_in_range(s, start, end) == 
               (if IsUpperCase(s.as_bytes().spec_index(start)) { 1 } else { 0 }) + 
               count_uppercase_in_range(s, start + 1, end));
        
        assert(count_uppercase_in_range(s, start, mid) == 
               (if IsUpperCase(s.as_bytes().spec_index(start)) { 1 } else { 0 }) + 
               count_uppercase_in_range(s, start + 1, mid));
        
        // Use the inductive hypothesis
        assert(count_uppercase_in_range(s, start + 1, end) == 
               count_uppercase_in_range(s, start + 1, mid) + count_uppercase_in_range(s, mid, end));
        
        // Combine the results
        assert(count_uppercase_in_range(s, start, end) == 
               (if IsUpperCase(s.as_bytes().spec_index(start)) { 1 } else { 0 }) + 
               count_uppercase_in_range(s, start + 1, mid) + count_uppercase_in_range(s, mid, end));
        
        assert(count_uppercase_in_range(s, start, end) == 
               count_uppercase_in_range(s, start, mid) + count_uppercase_in_range(s, mid, end));
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
        
        // Prove the relationship between counts before and after processing current character
        lemma_count_uppercase_append(s, 0, i as int, (i + 1) as int);
        
        assert(count_uppercase_in_range(s, 0, (i + 1) as int) == 
               count_uppercase_in_range(s, 0, i as int) + count_uppercase_in_range(s, i as int, (i + 1) as int));
        
        // Show that the single character range equals the IsUpperCase check
        assert(count_uppercase_in_range(s, i as int, (i + 1) as int) == 
               if IsUpperCase(s.as_bytes().spec_index(i as int)) { 1 } else { 0 });
        
        // Connect the byte value to the spec function
        assert(byte_val == s.as_bytes().spec_index(i as int));
        
        // Check if the byte value corresponds to an uppercase ASCII letter
        if 65 <= byte_val && byte_val <= 90 {
            assert(IsUpperCase(byte_val));
            assert(count_uppercase_in_range(s, i as int, (i + 1) as int) == 1);
            count = count + 1;
        } else {
            assert(!IsUpperCase(byte_val));
            assert(count_uppercase_in_range(s, i as int, (i + 1) as int) == 0);
        }
        
        // Establish the new invariant
        assert(count == count_uppercase_in_range(s, 0, i as int) + count_uppercase_in_range(s, i as int, (i + 1) as int));
        assert(count == count_uppercase_in_range(s, 0, (i + 1) as int));
        
        i = i + 1;
    }
    
    count
}

}