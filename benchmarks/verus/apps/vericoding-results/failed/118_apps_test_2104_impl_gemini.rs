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
fn char_from_digit_exec(d: u8) -> (c: char)
    requires 0 <= d < 10
    ensures c == char_from_digit(d as int)
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
    else { '9' }
}

fn int_to_string_pos_exec(n: u64) -> (s: Vec<char>)
    requires n > 0
    ensures s@ == int_to_string_pos(n as int)
    decreases n
{
    if n < 10 {
        vec![char_from_digit_exec(n as u8)]
    } else {
        let mut head = int_to_string_pos_exec(n / 10);
        head.push(char_from_digit_exec((n % 10) as u8));
        head
    }
}

fn int_to_string_exec(n: i64) -> (s: Vec<char>)
    ensures s@ == int_to_string(n as int)
{
    if n == 0 {
        vec!['0']
    } else if n > 0 {
        int_to_string_pos_exec(n as u64)
    } else {
        let mut res = vec!['-'];
        // n is derived from i8, so -n does not overflow i64 and fits in u64
        let pos_val = -n;
        let mut s_pos = int_to_string_pos_exec(pos_val as u64);
        res.append(&mut s_pos);
        res
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
    let l_int = l as int;
    let r_int = r as int;
    proof {
        assert((r_int - l_int) % 2 == 1);
        assert(l_int < r_int);
    }
    let num_pairs = (r_int - l_int + 1) / 2;

    let mut result: Vec<Vec<char>> = Vec::new();
    result.push(vec!['Y', 'E', 'S']);

    let mut i: int = 0;
    while i < num_pairs
        invariant
            0 <= i <= num_pairs,
            result.len() == 1 + i,
            result[0]@ == seq!['Y', 'E', 'S'],
            forall|j: int| 0 <= j < i ==>
                #[trigger] result[j+1]@ == int_to_string(l_int + 2 * j).add(seq![' ']).add(int_to_string(l_int + 2 * j + 1)),
        decreases num_pairs - i
    {
        let left_val = (l as i64) + 2 * (i as i64);
        let right_val = left_val + 1;

        let mut pair_str = int_to_string_exec(left_val);
        
        let left_seq = pair_str@;
        pair_str.push(' ');
        proof {
            vstd::seq::lemma_push_is_add(left_seq, ' ');
        }

        let mut right_str = int_to_string_exec(right_val);
        pair_str.append(&mut right_str);

        result.push(pair_str);
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}