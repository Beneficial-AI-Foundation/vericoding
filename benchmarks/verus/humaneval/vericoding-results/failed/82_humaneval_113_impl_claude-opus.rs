// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_all_digits(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> ('0' <= s[i] && s[i] <= '9')
}

spec fn count_odd_digits(s: Seq<char>) -> int
    recommends is_all_digits(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let digit = s[0] as int - '0' as int;
        let is_odd: int = if digit % 2 == 1 { 1 } else { 0 };
        is_odd + count_odd_digits(s.subrange(1, s.len() as int))
    }
}

spec fn int_to_string_func(n: int) -> Seq<char>
    recommends n >= 0
{
    if n == 0 {
        Seq::new(1, |i: int| '0')
    } else {
        int_to_string_rec(n, Seq::empty())
    }
}

spec fn format_message(count: int) -> Seq<char>
    recommends count >= 0
{
    let count_str = int_to_string_func(count);
    Seq::new(25, |i: int| 't').add(count_str).add(Seq::new(10, |i: int| 'n')).add(count_str).add(Seq::new(3, |i: int| 'g')).add(count_str).add(Seq::new(8, |i: int| ' ')).add(count_str).add(Seq::new(5, |i: int| 'n'))
}

spec fn int_to_string_rec(n: int, acc: Seq<char>) -> Seq<char>
    recommends n >= 0
    decreases n
    when n > 0
{
    if n == 0 {
        acc
    } else {
        let digit = n % 10;
        let digit_char = ('0' as int + digit) as char;
        int_to_string_rec(n / 10, Seq::new(1, |i: int| digit_char).add(acc))
    }
}

fn int_to_string(n: u32) -> (s: Vec<char>)
    requires n >= 0
{
    assume(false);
    vec!['0']
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): implement count_odd_digits_exec and format_message_exec */
fn count_odd_digits_exec(s: &Vec<char>) -> (count: u32)
    requires is_all_digits(s@),
    ensures count == count_odd_digits(s@),
{
    let mut count = 0u32;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count == count_odd_digits(s@.subrange(0, i as int)),
    {
        let digit = s[i] as u8 - '0' as u8;
        if digit % 2 == 1 {
            count += 1;
        }
        i += 1;
    }
    count
}

fn format_message_exec(count: u32) -> (result: Vec<char>)
    ensures result@ == format_message(count as int),
{
    // Create the message "the number of odd elements in the string of the string of the string of the string of the input."
    let mut result = Vec::new();
    
    // "the number of odd elements "
    result.push('t');
    result.push('h');
    result.push('e');
    result.push(' ');
    result.push('n');
    result.push('u');
    result.push('m');
    result.push('b');
    result.push('e');
    result.push('r');
    result.push(' ');
    result.push('o');
    result.push('f');
    result.push(' ');
    result.push('o');
    result.push('d');
    result.push('d');
    result.push(' ');
    result.push('e');
    result.push('l');
    result.push('e');
    result.push('m');
    result.push('e');
    result.push('n');
    result.push('t');
    result.push('s');
    result.push(' ');
    
    // Add count as string
    if count == 0 {
        result.push('0');
    } else {
        let mut n = count;
        let mut digits = Vec::new();
        while n > 0 {
            let digit = (n % 10) as u8;
            digits.push(('0' as u8 + digit) as char);
            n = n / 10;
        }
        let mut j = digits.len();
        while j > 0 {
            j = j - 1;
            result.push(digits[j]);
        }
    }
    
    // "n the string "
    result.push('n');
    result.push(' ');
    result.push('t');
    result.push('h');
    result.push('e');
    result.push(' ');
    result.push('s');
    result.push('t');
    result.push('r');
    result.push('i');
    result.push('n');
    result.push('g');
    result.push(' ');
    
    // Add count again
    if count == 0 {
        result.push('0');
    } else {
        let mut n = count;
        let mut digits = Vec::new();
        while n > 0 {
            let digit = (n % 10) as u8;
            digits.push(('0' as u8 + digit) as char);
            n = n / 10;
        }
        let mut j = digits.len();
        while j > 0 {
            j = j - 1;
            result.push(digits[j]);
        }
    }
    
    // "of the string "
    result.push('o');
    result.push('f');
    result.push(' ');
    result.push('t');
    result.push('h');
    result.push('e');
    result.push(' ');
    result.push('s');
    result.push('t');
    result.push('r');
    result.push('i');
    result.push('n');
    result.push('g');
    result.push(' ');
    
    // Add count again
    if count == 0 {
        result.push('0');
    } else {
        let mut n = count;
        let mut digits = Vec::new();
        while n > 0 {
            let digit = (n % 10) as u8;
            digits.push(('0' as u8 + digit) as char);
            n = n / 10;
        }
        let mut j = digits.len();
        while j > 0 {
            j = j - 1;
            result.push(digits[j]);
        }
    }
    
    // "of the string "
    result.push('o');
    result.push('f');
    result.push(' ');
    result.push('t');
    result.push('h');
    result.push('e');
    result.push(' ');
    result.push('s');
    result.push('t');
    result.push('r');
    result.push('i');
    result.push('n');
    result.push('g');
    result.push(' ');
    
    // Add count again
    if count == 0 {
        result.push('0');
    } else {
        let mut n = count;
        let mut digits = Vec::new();
        while n > 0 {
            let digit = (n % 10) as u8;
            digits.push(('0' as u8 + digit) as char);
            n = n / 10;
        }
        let mut j = digits.len();
        while j > 0 {
            j = j - 1;
            result.push(digits[j]);
        }
    }
    
    // "of the input."
    result.push('o');
    result.push('f');
    result.push(' ');
    result.push('t');
    result.push('h');
    result.push('e');
    result.push(' ');
    result.push('i');
    result.push('n');
    result.push('p');
    result.push('u');
    result.push('t');
    result.push('.');
    
    result
}
// </vc-helpers>

// <vc-spec>
fn odd_count(lst: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    requires forall|i: int| #![auto] 0 <= i < lst.len() ==> is_all_digits(lst[i as int]@),
    ensures result.len() == lst.len(),
    ensures forall|i: int| #![auto] 0 <= i < result.len() ==> result[i as int]@ == format_message(count_odd_digits(lst[i as int]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implement without assume statements */
    let mut result = Vec::new();
    let mut i = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j as int]@ == format_message(count_odd_digits(lst[j as int]@)),
    {
        let count = count_odd_digits_exec(&lst[i]);
        let msg = format_message_exec(count);
        result.push(msg);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}