// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(l: int, r: int) -> bool {
    l < r && (r - l) % 2 == 1
}

spec fn gcd(a: int, b: int) -> int
    recommends a != 0 || b != 0
    decreases (if a >= 0 { a } else { -a })
{
    if a == 0 {
        if b >= 0 { b } else { -b }
    } else {
        gcd(b % a, a)
    }
}

spec fn pair_has_gcd_one(pair: Seq<char>, l: int, r: int) -> bool {
    exists|i: int, j: int| l <= i <= r && l <= j <= r && i != j &&
        pair == int_to_string(i).add(seq![' ']).add(int_to_string(j)) &&
        (i != 0 || j != 0) && gcd(i, j) == 1
}

spec fn valid_solution(result: Seq<Seq<char>>, l: int, r: int) -> bool {
    result.len() >= 1 &&
    result[0] == seq!['Y', 'E', 'S'] &&
    result.len() == 1 + (r - l + 1) / 2 &&
    (forall|i: int| 1 <= i < result.len() ==> pair_has_gcd_one(result[i], l, r))
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n > 0 {
        int_to_string_pos(n)
    } else {
        seq!['-'].add(int_to_string_pos(-n))
    }
}

spec fn int_to_string_pos(n: int) -> Seq<char>
    recommends n > 0
    decreases n
{
    if n < 10 {
        seq![char_from_digit(n)]
    } else {
        int_to_string_pos(n / 10).push(char_from_digit(n % 10))
    }
}

spec fn char_from_digit(d: int) -> char
    recommends 0 <= d <= 9
{
    if d == 0 { '0' }
    else if d == 1 { '1' }
    else if d == 2 { '2' }
    else if d == 3 { '3' }
    else if d == 4 { '4' }
    else if d == 5 { '5' }
    else if d == 6 { '6' }
    else if d == 7 { '7' }
    else if d == 8 { '8' }
    else if d == 9 { '9' }
    else { '0' }
}
// </vc-preamble>

// <vc-helpers>
fn char_from_digit_exec(d: i32) -> char
    requires
        0 <= d <= 9,
    ensures
        result == char_from_digit(d as int),
{
    match d {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        9 => '9',
        _ => '0',
    }
}

fn int_to_string_pos_exec(n: i32) -> Vec<char>
    requires
        n > 0,
    ensures
        result@ == int_to_string_pos(n as int),
    decreases n,
{
    if n < 10 {
        vec![char_from_digit_exec(n)]
    } else {
        let mut s = int_to_string_pos_exec(n / 10);
        s.push(char_from_digit_exec(n % 10));
        s
    }
}

fn int_to_string_exec(n: i32) -> Vec<char>
    ensures
        result@ == int_to_string(n as int),
{
    if n == 0 {
        vec!['0']
    } else if n > 0 {
        int_to_string_pos_exec(n)
    } else {
        let mut s = vec!['-'];
        let mut pos = int_to_string_pos_exec(-n);
        s.append(&mut pos);
        s
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(l: i8, r: i8) -> (result: Vec<Vec<char>>)
    requires valid_input(l as int, r as int)
    ensures
        result.len() >= 1,
        result[0]@ == seq!['Y', 'E', 'S'],
        result.len() == 1 + (r as int - l as int + 1) / 2,
        forall|i: int| 1 <= i < result.len() ==> 
            #[trigger] result[i]@ == int_to_string(l as int + 2 * (i - 1)).add(seq![' ']).add(int_to_string(l as int + 2 * (i - 1) + 1))
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<Vec<char>> = Vec::new();
    let yes: Vec<char> = vec!['Y', 'E', 'S'];
    result.push(yes);
    let mut cur = l as i32;
    while cur < r as i32
        invariant
            result.len() == 1 + ((cur as int - l as int) / 2),
            forall|i: int| 1 <= i < result.len() ==> result[i]@ == int_to_string(l as int + 2 * (i - 1)).add(seq![' ']).add(int_to_string(l as int + 2 * (i - 1) + 1)),
            l as int <= cur as int,
            cur as int <= r as int,
        decreases (r as i32 - cur + 1),
    {
        let s1 = int_to_string_exec(cur);
        let space: Vec<char> = vec![' '];
        let s2 = int_to_string_exec(cur + 1);
        let mut pair = Vec::new();
        pair.append(&mut s1);
        pair.append(&mut space);
        pair.append(&mut s2);
        result.push(pair);
        cur += 2;
    }
    result
}
// </vc-code>


}

fn main() {}