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
fn int_to_string_recursive(n: u32, acc: Vec<char>) -> (s: Vec<char>)
    requires n >= 0,
    ensures s@ == int_to_string_rec(n as int, acc@),
    decreases n
{
    if n == 0 {
        acc
    } else {
        let digit = (n % 10) as u8;
        let digit_char = ('0' as u8 + digit) as char;
        let mut new_acc = Vec::new();
        new_acc.push(digit_char);
        new_acc.extend(acc);
        int_to_string_recursive(n / 10, new_acc)
    }
}

fn int_to_string(n: u32) -> (s: Vec<char>)
    requires n >= 0,
    ensures s@ == int_to_string_func(n as int)
{
    if n == 0 {
        vec!['0']
    } else {
        int_to_string_recursive(n, Vec::new())
    }
}

fn format_message_impl(count: u32) -> (s: Vec<char>)
    requires count >= 0,
    ensures s@ == format_message(count as int)
{
    let count_str = int_to_string(count);
    let mut result = Vec::new();
    
    result.extend(vec!['t'; 25]);
    result.extend(count_str.clone());
    result.extend(vec!['n'; 10]);
    result.extend(count_str.clone());
    result.extend(vec!['g'; 3]);
    result.extend(count_str.clone());
    result.extend(vec![' '; 8]);
    result.extend(count_str.clone());
    result.extend(vec!['n'; 5]);
    
    result
}

fn count_odd_digits_impl(s: Vec<char>) -> (count: u32)
    requires is_all_digits(s@),
    ensures count as int == count_odd_digits(s@)
{
    let mut count = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_odd_digits(s@.subrange(0, i as int)),
            is_all_digits(s@)
        decreases s.len() - i
    {
        let digit_char = s[i];
        let digit = digit_char as u32 - '0' as u32;
        
        if digit % 2 == 1 {
            count += 1;
        }
        
        i += 1;
    }
    
    count
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
    /* code modified by LLM (iteration 5): Fixed compilation error by moving ensures clauses to proper function signature */
    let mut result = Vec::with_capacity(lst.len());
    let mut i = 0;
    
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as int]@ == format_message(count_odd_digits(lst[j as int]@)),
            forall|k: int| 0 <= k < lst.len() ==> is_all_digits(lst[k as int]@)
        decreases lst.len() - i
    {
        let item = lst[i].clone();
        let odd_count = count_odd_digits_impl(item);
        let formatted = format_message_impl(odd_count);
        result.push(formatted);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}