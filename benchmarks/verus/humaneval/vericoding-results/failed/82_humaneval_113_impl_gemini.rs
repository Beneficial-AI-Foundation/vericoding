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
proof fn lemma_count_odd_digits_concat(s1: Seq<char>, s2: Seq<char>)
    requires
        is_all_digits(s1),
        is_all_digits(s2),
    ensures count_odd_digits(s1.add(s2)) == count_odd_digits(s1) + count_odd_digits(s2)
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_count_odd_digits_concat(s1.subrange(1, s1.len() as int), s2);
    }
}

fn count_odd_digits_exec(s: &Vec<char>) -> (c: u32)
    requires is_all_digits(s@)
    ensures c as int == count_odd_digits(s@)
{
    let mut count: u32 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_all_digits(s@),
            count as int == count_odd_digits(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        let digit = s[i] as int - '0' as int;
        proof {
            let s1 = s@.subrange(0, i as int);
            let s2 = s@.subrange(i as int, (i + 1) as int);
            assert(s@.subrange(0, (i+1) as int) === s1.add(s2));
            lemma_count_odd_digits_concat(s1, s2);
        }
        if digit % 2 == 1 {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

fn int_to_string_rec_impl(n: u32, acc: Vec<char>) -> (s: Vec<char>)
    ensures s@ == int_to_string_rec(n as int, acc@),
    decreases n
{
    if n == 0 {
        acc
    } else {
        let digit_char = ('0' as u32 + (n % 10)) as char;
        let mut new_acc = vec![digit_char];
        new_acc.extend(acc);
        int_to_string_rec_impl(n / 10, new_acc)
    }
}

fn int_to_string_impl(n: u32) -> (s: Vec<char>)
    ensures s@ == int_to_string_func(n as int)
{
    if n == 0 {
        vec!['0']
    } else {
        int_to_string_rec_impl(n, Vec::new())
    }
}

fn repeat_char_exec(c: char, n: u32) -> (res: Vec<char>)
    ensures res@ == Seq::new(n as int, |i: int| c)
{
    let mut res = Vec::new();
    let mut i: u32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            res@ == Seq::new(i as int, |j: int| c),
        decreases n - i
    {
        res.push(c);
        i = i + 1;
    }
    res
}

fn format_message_exec(count: u32) -> (msg: Vec<char>)
    ensures msg@ == format_message(count as int)
{
    let count_str = int_to_string_impl(count);
    let mut result = repeat_char_exec('t', 25);
    result.extend_from_slice(count_str.as_slice());
    result.extend(repeat_char_exec('n', 10));
    result.extend_from_slice(count_str.as_slice());
    result.extend(repeat_char_exec('g', 3));
    result.extend_from_slice(count_str.as_slice());
    result.extend(repeat_char_exec(' ', 8));
    result.extend_from_slice(count_str.as_slice());
    result.extend(repeat_char_exec('n', 5));
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            0 <= i <= lst.len(),
            forall|j: int| 0 <= j < lst.len() ==> is_all_digits(lst[j as int]@),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as int]@ == format_message(count_odd_digits(lst[j as int]@)),
        decreases lst.len() - i
    {
        let s = &lst[i];
        let count = count_odd_digits_exec(s);
        let msg = format_message_exec(count);
        result.push(msg);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}