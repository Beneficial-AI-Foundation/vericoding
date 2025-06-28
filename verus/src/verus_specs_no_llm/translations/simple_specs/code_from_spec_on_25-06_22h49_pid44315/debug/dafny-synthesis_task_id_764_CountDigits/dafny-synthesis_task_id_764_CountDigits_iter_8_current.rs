use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int && c as int <= 57
}

// Executable version of digit checking
fn is_digit_exec(c: char) -> (result: bool)
    ensures result == IsDigit(c)
{
    let code = c as u32;
    48 <= code && code <= 57
}

spec fn count_digits_in_range(s: Seq<char>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else if start < 0 || start >= s.len() {
        0
    } else {
        let current_count = if IsDigit(s[start]) { 1 } else { 0 };
        current_count + count_digits_in_range(s, start + 1, end)
    }
}

// Helper lemma to prove the inductive step
proof fn lemma_count_digits_step(s: Seq<char>, i: int)
    requires 
        0 <= i < s.len(),
    ensures
        count_digits_in_range(s, 0, i + 1) == 
        count_digits_in_range(s, 0, i) + (if IsDigit(s[i]) { 1 } else { 0 }),
    decreases i
{
    if i == 0 {
        // Base case
        assert(count_digits_in_range(s, 0, 0) == 0);
        assert(count_digits_in_range(s, 1, 1) == 0);
    } else {
        // Inductive case
        lemma_count_digits_step(s, i - 1);
        
        // Prove that count_digits_in_range(s, 0, i+1) can be split
        assert(count_digits_in_range(s, 0, i + 1) == 
               if IsDigit(s[0]) { 1 } else { 0 } + count_digits_in_range(s, 1, i + 1));
        
        // And count_digits_in_range(s, 0, i) can be split similarly
        assert(count_digits_in_range(s, 0, i) == 
               if IsDigit(s[0]) { 1 } else { 0 } + count_digits_in_range(s, 1, i));
        
        // The difference is count_digits_in_range(s, 1, i+1) - count_digits_in_range(s, 1, i)
        // which equals IsDigit(s[i]) by the recursive definition
    }
}

fn CountDigits(s: &Seq<char>) -> (count: usize)
    ensures
        count >= 0,
        count == count_digits_in_range(*s, 0, s.len() as int),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count >= 0,
            count == count_digits_in_range(*s, 0, i as int),
    {
        // Use the lemma to prove the loop invariant will be maintained
        proof {
            if i < s.len() {
                lemma_count_digits_step(*s, i as int);
            }
        }
        
        if is_digit_exec(s[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}