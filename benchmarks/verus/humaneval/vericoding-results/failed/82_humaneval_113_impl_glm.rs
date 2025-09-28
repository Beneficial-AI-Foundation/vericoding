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
fn int_to_string_exec(n: u32) -> (s: Vec<char>)
    requires n >= 0
    decreases n
{
    if n == 0 {
        vec!['0']
    } else {
        let digit = n % 10;
        let digit_char = ('0' as u8 + digit as u8) as char;
        let rest = int_to_string_exec(n / 10);
        let mut result = rest;
        result.push(digit_char);
        result
    }
}

fn count_odd_digits_exec(s: &Vec<char>) -> (count: u32)
{
    let mut count = 0;
    let mut i = 0;
    while i < s.len()
        invariant 0 <= i <= s.len(),
        decreases s.len() - i
    {
        let c = s[i];
        if '0' <= c && c <= '9' {
            let digit = (c as u8 - '0' as u8) as u32;
            if digit % 2 == 1 {
                count += 1;
            }
        }
        i += 1;
    }
    count
}

fn format_message_exec(count: u32) -> (s: Vec<char>)
{
    let mut result = Vec::new();
    // 25 't's
    for _ in 0..25 {
        result.push('t');
    }
    // count string
    let count_str = int_to_string_exec(count);
    result.extend(count_str);
    // 10 'n's
    for _ in 0..10 {
        result.push('n');
    }
    // count string again
    let count_str2 = int_to_string_exec(count);
    result.extend(count_str2);
    // 3 'g's
    for _ in 0..3 {
        result.push('g');
    }
    // count string again
    let count_str3 = int_to_string_exec(count);
    result.extend(count_str3);
    // 8 spaces
    for _ in 0..8 {
        result.push(' ');
    }
    // count string again
    let count_str4 = int_to_string_exec(count);
    result.extend(count_str4);
    // 5 'n's
    for _ in 0..5 {
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
    /* code modified by LLM (iteration 2): fixed duplicate ensures by removing function signature */
    let mut result = Vec::new();
    let mut i = 0;
    while i < lst.len()
        invariant i <= lst.len(),
        invariant result.len() == i,
        invariant forall|j: int| 0 <= j < i ==> result[j as int]@ == format_message(count_odd_digits(lst[j as int]@)),
        decreases lst.len() - i
    {
        let s = &lst[i];
        let count = count_odd_digits_exec(s);
        let msg = format_message_exec(count);
        result.push(msg);
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}