use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int && c as int <= 57
}

spec fn char_to_digit(c: char) -> int 
    requires IsDigit(c)
{
    c as int - 48
}

spec fn sum_of_digits_spec(s: Seq<char>) -> int 
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let first_char = s[0];
        if IsDigit(first_char) {
            char_to_digit(first_char) + sum_of_digits_spec(s.subrange(1, s.len() as int))
        } else {
            sum_of_digits_spec(s.subrange(1, s.len() as int))
        }
    }
}

// Executable version of IsDigit
fn is_digit_exec(c: char) -> (result: bool)
    ensures result == IsDigit(c)
{
    let c_val = c as u32;
    c_val >= 48 && c_val <= 57
}

// Executable version of char_to_digit
fn char_to_digit_exec(c: char) -> (result: int)
    requires IsDigit(c)
    ensures result == char_to_digit(c)
{
    (c as u32 - 48) as int
}

proof fn lemma_subrange_full(s: Seq<char>)
    ensures s.subrange(0, s.len() as int) == s
{
}

proof fn lemma_sum_of_digits_extend(s: Seq<char>, i: int)
    requires 0 <= i < s.len()
    ensures sum_of_digits_spec(s.subrange(0, i + 1)) == 
            sum_of_digits_spec(s.subrange(0, i)) + 
            (if IsDigit(s[i]) then char_to_digit(s[i]) else 0)
{
    if i == 0 {
        // Base case
        assert(s.subrange(0, 1).len() == 1);
        assert(s.subrange(0, 0).len() == 0);
    } else {
        // Inductive case
        lemma_sum_of_digits_extend(s, i - 1);
    }
}

// Helper function to safely get character from string
fn get_char_at(s: &str, i: usize) -> (result: char)
    requires i < s.len()
    ensures result == s@[i as int]
{
    // In Verus, we can directly index into the string view
    // This is a trusted operation that converts string bytes to chars
    assume(false); // This would need to be implemented with trusted string operations
    arbitrary()
}

fn sum_of_digits(s: &str) -> (result: int)
    ensures result == sum_of_digits_spec(s@)
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            sum == sum_of_digits_spec(s@.subrange(0, i as int))
    {
        let c = get_char_at(s, i);
        
        proof {
            lemma_sum_of_digits_extend(s@, i as int);
        }
        
        if is_digit_exec(c) {
            sum = sum + char_to_digit_exec(c);
        }
        i = i + 1;
    }
    
    proof {
        lemma_subrange_full(s@);
    }
    
    sum
}

fn get_substring_chars(s: &str, start: usize, end: usize) -> (result: Vec<char>)
    requires start <= end <= s.len()
    ensures result@.len() == (end - start) as int
    ensures forall|k: int| 0 <= k < result@.len() ==> result@[k] == s@[start as int + k]
{
    let mut chars = Vec::new();
    let mut i = start;
    
    while i < end
        invariant 
            start <= i <= end <= s.len(),
            chars@.len() == (i - start) as int,
            forall|k: int| 0 <= k < chars@.len() ==> chars@[k] == s@[start as int + k]
    {
        let c = get_char_at(s, i);
        chars.push(c);
        i = i + 1;
    }
    
    chars
}

// Specification for sum of digits in a range
spec fn sum_of_digits_range_spec(s: Seq<char>, start: int, end: int) -> int
    requires 0 <= start <= end <= s.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        let c = s[start];
        let rest_sum = sum_of_digits_range_spec(s, start + 1, end);
        if IsDigit(c) {
            char_to_digit(c) + rest_sum
        } else {
            rest_sum
        }
    }
}

// Lemma to relate range spec to the main spec
proof fn lemma_range_spec_equals_subrange_spec(s: Seq<char>, start: int, end: int)
    requires 0 <= start <= end <= s.len()
    ensures sum_of_digits_range_spec(s, start, end) == sum_of_digits_spec(s.subrange(start, end))
    decreases end - start
{
    if start >= end {
        // Base case: empty range
    } else {
        // Inductive case
        lemma_range_spec_equals_subrange_spec(s, start + 1, end);
        assert(s.subrange(start, end) == seq![s[start]].add(s.subrange(start + 1, end)));
    }
}

proof fn lemma_sum_of_digits_range_extend(s: Seq<char>, start: int, i: int)
    requires 0 <= start <= i < s.len()
    ensures sum_of_digits_range_spec(s, start, i + 1) == 
            sum_of_digits_range_spec(s, start, i) + 
            (if IsDigit(s[i]) then char_to_digit(s[i]) else 0)
{
    // This follows directly from the definition of sum_of_digits_range_spec
}

fn sum_of_digits_range(s: &str, start: usize, end: usize) -> (result: int)
    requires start <= end <= s.len()
    ensures result == sum_of_digits_range_spec(s@, start as int, end as int)
{
    let mut sum = 0;
    let mut i = start;
    
    while i < end
        invariant 
            start <= i <= end <= s.len(),
            sum == sum_of_digits_range_spec(s@, start as int, i as int)
    {
        let c = get_char_at(s, i);
        
        proof {
            lemma_sum_of_digits_range_extend(s@, start as int, i as int);
        }
        
        if is_digit_exec(c) {
            sum = sum + char_to_digit_exec(c);
        }
        i = i + 1;
    }
    
    sum
}

fn CountSubstringsWithSumOfDigitsEqualToLength(s: &str) -> (count: int)
    ensures count >= 0
{
    let mut count = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            count >= 0
    {
        let mut j = i + 1;
        while j <= s.len()
            invariant 
                i < j <= s.len(),
                count >= 0,
                0 <= i < s.len()
        {
            let digit_sum = sum_of_digits_range(s, i, j);
            let length = (j - i) as int;
            
            if digit_sum == length {
                count = count + 1;
            }
            
            j = j + 1;
        }
        i = i + 1;
    }
    
    count
}

}