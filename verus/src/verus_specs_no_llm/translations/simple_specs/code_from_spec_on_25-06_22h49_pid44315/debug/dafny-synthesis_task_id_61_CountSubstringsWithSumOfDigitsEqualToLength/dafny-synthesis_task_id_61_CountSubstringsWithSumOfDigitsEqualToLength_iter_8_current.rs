use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsDigit(c: char) -> bool {
    '0' <= c && c <= '9'
}

spec fn char_to_digit(c: char) -> int 
    requires IsDigit(c)
{
    c as int - '0' as int
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
    '0' <= c && c <= '9'
}

// Executable version of char_to_digit
fn char_to_digit_exec(c: char) -> (result: int)
    requires IsDigit(c)
    ensures result == char_to_digit(c)
{
    (c as u32 - '0' as u32) as int
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
    decreases i
{
    if i == 0 {
        // Base case
        assert(s.subrange(0, 1).len() == 1);
        assert(s.subrange(0, 0).len() == 0);
        assert(s.subrange(0, 1)[0] == s[0]);
    } else {
        // Inductive case
        lemma_sum_of_digits_extend(s, i - 1);
        assert(s.subrange(0, i + 1).subrange(1, (i + 1) as int) == s.subrange(1, (i + 1) as int));
    }
}

// Simple conversion from string to vector of chars
fn string_to_vec_char(s: &str) -> (result: Vec<char>)
    ensures result@.len() == s@.len()
    ensures forall|i: int| 0 <= i < s@.len() ==> result@[i] == s@[i]
{
    let mut chars = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            chars@.len() == i,
            forall|k: int| 0 <= k < i ==> chars@[k] == s@[k]
    {
        let c = s.get_char(i);
        chars.push(c);
        i = i + 1;
    }
    
    chars
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
        let c = s.get_char(i);
        
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
        assert(s.subrange(start, end).len() == 0);
    } else {
        // Inductive case
        lemma_range_spec_equals_subrange_spec(s, start + 1, end);
        assert(s.subrange(start, end)[0] == s[start]);
        assert(s.subrange(start, end).subrange(1, (end - start) as int) == s.subrange(start + 1, end));
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
        let c = s.get_char(i);
        
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