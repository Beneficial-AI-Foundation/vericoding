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
proof fn lemma_count_odd_digits_bound(s: Seq<char>)
    requires is_all_digits(s),
    ensures 0 <= count_odd_digits(s) <= s.len(),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_count_odd_digits_bound(s.subrange(1, s.len() as int));
    }
}

proof fn lemma_int_to_string_correct(n: u32)
    ensures int_to_string(n)@.len() > 0,
    ensures is_all_digits(int_to_string(n)@)
{
}

fn int_to_string(n: u32) -> (s: Vec<char>)
    requires n >= 0,
    ensures s@.len() > 0,
    ensures is_all_digits(s@)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut digits = Vec::new();
        let mut num = n;
        
        while num > 0
            invariant
                num >= 0,
                digits.len() >= 0
        {
            let digit = (num % 10) as u8;
            let digit_char = (b'0' + digit) as char;
            digits.push(digit_char);
            num = num / 10;
        }
        
        digits.reverse();
        digits
    }
}

fn count_odd_digits_impl(s: &Vec<char>) -> (result: u32)
    requires is_all_digits(s@),
    ensures result as int == count_odd_digits(s@)
{
    let mut count = 0u32;
    
    for i in 0..s.len()
        invariant
            count as int == count_odd_digits(s@.subrange(0, i as int))
    {
        let digit = s[i] as u8 - b'0';
        if digit % 2 == 1 {
            count += 1;
        }
    }
    
    count
}

fn format_message_impl(count: u32) -> (result: Vec<char>)
    requires count >= 0,
    ensures result@.len() > 0,
    ensures result@ == format_message(count as int)
{
    let count_str = int_to_string(count);
    let mut result = Vec::new();
    
    for i in 0..25
        invariant result.len() == i,
        invariant forall|j: int| 0 <= j < i ==> result[j] == 't'
    {
        result.push('t');
    }
    
    result.append(&mut count_str.clone());
    
    for i in 0..10
        invariant result.len() == 25 + count_str.len() + i
    {
        result.push('n');
    }
    
    result.append(&mut count_str.clone());
    
    for i in 0..3
        invariant result.len() == 25 + count_str.len() + 10 + count_str.len() + i
    {
        result.push('g');
    }
    
    result.append(&mut count_str.clone());
    
    for i in 0..8
        invariant result.len() == 25 + count_str.len() + 10 + count_str.len() + 3 + count_str.len() + i
    {
        result.push(' ');
    }
    
    result.append(&mut count_str.clone());
    
    for i in 0..5
        invariant result.len() == 25 + count_str.len() + 10 + count_str.len() + 3 + count_str.len() + 8 + count_str.len() + i
    {
        result.push('n');
    }
    
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
    /* code modified by LLM (iteration 5): implemented main function logic */
    let mut result = Vec::new();
    
    for i in 0..lst.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j]@ == format_message(count_odd_digits(lst[j]@))
    {
        let count = count_odd_digits_impl(&lst[i]);
        proof {
            lemma_count_odd_digits_bound(lst[i as int]@);
        }
        let formatted = format_message_impl(count);
        result.push(formatted);
    }
    
    result
}
// </vc-code>


}

fn main() {}