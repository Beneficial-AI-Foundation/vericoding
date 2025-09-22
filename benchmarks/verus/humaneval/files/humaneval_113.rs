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
// </vc-helpers>

// <vc-spec>
fn odd_count(lst: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    requires forall|i: int| #![auto] 0 <= i < lst.len() ==> is_all_digits(lst[i as int]@),
    ensures 
        result.len() == lst.len(),
        forall|i: int| #![auto] 0 <= i < result.len() ==> result[i as int]@ == format_message(count_odd_digits(lst[i as int]@))
// </vc-spec>
// <vc-code>
{
    assume(false);
    vec![]
}
// </vc-code>


}

fn main() {}