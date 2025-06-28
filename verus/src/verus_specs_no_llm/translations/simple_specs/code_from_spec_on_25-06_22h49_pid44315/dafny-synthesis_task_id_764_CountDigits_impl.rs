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

// Simplified lemma that directly proves what we need for the loop
proof fn lemma_count_digits_extend(s: Seq<char>, i: int)
    requires 
        0 <= i < s.len(),
    ensures
        count_digits_in_range(s, 0, i + 1) == 
        count_digits_in_range(s, 0, i) + count_digits_in_range(s, i, i + 1),
{
    if i == 0 {
        // Base case: count_digits_in_range(s, 0, 1) == count_digits_in_range(s, 0, 0) + count_digits_in_range(s, 0, 1)
        assert(count_digits_in_range(s, 0, 0) == 0);
    } else {
        // Recursive case: use the structure of the recursive definition
        lemma_count_digits_extend(s, i - 1);
    }
}

proof fn lemma_single_char_count(s: Seq<char>, i: int)
    requires 
        0 <= i < s.len(),
    ensures
        count_digits_in_range(s, i, i + 1) == if IsDigit(s[i]) { 1 } else { 0 },
{
    // This follows from the definition: when start = i and end = i + 1,
    // we have exactly one character to check
    assert(i < i + 1);
    assert(i >= 0 && i < s.len());
}

proof fn lemma_count_digits_base_case(s: Seq<char>)
    ensures count_digits_in_range(s, 0, 0) == 0
{
    // Base case: empty range has 0 digits
}

fn CountDigits(s: &Seq<char>) -> (count: usize)
    ensures
        count as int == count_digits_in_range(*s, 0, s.len() as int),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    proof {
        lemma_count_digits_base_case(*s);
    }
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_digits_in_range(*s, 0, i as int),
    {
        proof {
            // Prove that extending the range by one character updates the count correctly
            lemma_count_digits_extend(*s, i as int);
            lemma_single_char_count(*s, i as int);
        }
        
        if is_digit_exec(s[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}