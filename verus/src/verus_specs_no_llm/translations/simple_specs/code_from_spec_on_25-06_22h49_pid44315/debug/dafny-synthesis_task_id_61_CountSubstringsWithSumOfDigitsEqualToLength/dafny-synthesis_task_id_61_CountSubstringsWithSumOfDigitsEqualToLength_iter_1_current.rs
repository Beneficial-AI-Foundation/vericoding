use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    48 <= c as int <= 57
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
        if IsDigit(c) {
            sum += char_to_digit(c);
        }
        i += 1;
    }
    
    assert(s.subrange(0, s.len() as int) =~= s);
    sum
}

fn CountSubstringsWithSumOfDigitsEqualToLength(s: String) -> (count: int)
    ensures count >= 0
{
    let s_ref = s.as_str();
    let mut count = 0;
    let mut i = 0;
    
    while i < s_ref.len()
        invariant 
            0 <= i <= s_ref.len(),
            count >= 0
    {
        let mut j = i + 1;
        while j <= s_ref.len()
            invariant 
                i < j <= s_ref.len(),
                count >= 0
        {
            let substring = s_ref.subrange(i as int, j as int);
            let digit_sum = sum_of_digits(substring);
            let length = substring.len();
            
            if digit_sum == length {
                count += 1;
            }
            
            j += 1;
        }
        i += 1;
    }
    
    count
}

}