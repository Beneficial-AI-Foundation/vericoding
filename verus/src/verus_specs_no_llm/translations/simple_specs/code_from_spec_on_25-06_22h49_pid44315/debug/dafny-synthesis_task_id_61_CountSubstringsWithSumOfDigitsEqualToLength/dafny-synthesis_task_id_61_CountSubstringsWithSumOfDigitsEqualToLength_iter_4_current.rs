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
        assert(s.subrange(0, 1) == seq![s[0]]);
        assert(s.subrange(0, 0) == seq![]);
    } else {
        // Inductive case
        lemma_sum_of_digits_extend(s, i - 1);
    }
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
        let c = s.as_bytes()[i] as char;
        
        proof {
            assert(s@[i as int] == c);
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
{
    let mut chars = Vec::new();
    let mut i = start;
    
    while i < end
        invariant 
            start <= i <= end <= s.len(),
            chars@.len() == (i - start) as int
    {
        chars.push(s.as_bytes()[i] as char);
        i = i + 1;
    }
    
    chars
}

fn sum_of_digits_range(s: &str, start: usize, end: usize) -> (result: int)
    requires start <= end <= s.len()
{
    let mut sum = 0;
    let mut i = start;
    
    while i < end
        invariant 
            start <= i <= end <= s.len(),
            sum >= 0
    {
        let c = s.as_bytes()[i] as char;
        
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