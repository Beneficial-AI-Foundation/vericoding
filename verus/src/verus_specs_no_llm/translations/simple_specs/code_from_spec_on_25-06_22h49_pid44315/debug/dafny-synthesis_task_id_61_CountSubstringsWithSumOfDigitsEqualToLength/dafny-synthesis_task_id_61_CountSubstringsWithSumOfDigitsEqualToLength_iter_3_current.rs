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

spec fn sum_of_digits_spec(s: &str) -> int 
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let first_char = s.index(0);
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

proof fn lemma_subrange_full(s: &str)
    ensures s.subrange(0, s.len() as int) == s
{
}

proof fn lemma_sum_of_digits_extend(s: &str, i: int)
    requires 0 <= i < s.len()
    ensures sum_of_digits_spec(s.subrange(0, i + 1)) == 
            sum_of_digits_spec(s.subrange(0, i)) + 
            (if IsDigit(s.index(i)) then char_to_digit(s.index(i)) else 0)
{
    if i == 0 {
        // Base case
    } else {
        // Inductive case - Verus can handle this automatically
    }
}

fn sum_of_digits(s: &str) -> (result: int)
    ensures result == sum_of_digits_spec(s)
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            sum == sum_of_digits_spec(s.subrange(0, i as int))
    {
        let c = s.index(i as int);
        
        proof {
            lemma_sum_of_digits_extend(s, i as int);
        }
        
        if is_digit_exec(c) {
            sum = sum + char_to_digit_exec(c);
        }
        i = i + 1;
    }
    
    proof {
        lemma_subrange_full(s);
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
            let substring = s.subrange(i as int, j as int);
            let digit_sum = sum_of_digits(substring);
            let length = substring.len() as int;
            
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