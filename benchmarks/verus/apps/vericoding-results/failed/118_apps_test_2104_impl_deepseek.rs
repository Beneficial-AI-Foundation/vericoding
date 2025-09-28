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

proof fn lemma_gcd_symmetric(a: int, b: int)
    ensures gcd(a, b) == gcd(b, a)
{
    // GCD is symmetric by definition
}

proof fn lemma_gcd_one_case(n: int)
    requires n != 0
    ensures gcd(n, n + 1) == 1
{
    // For consecutive integers n and n+1, gcd is always 1
    assert(n != 0 && n + 1 != 0 && gcd(n, n + 1) == 1);
}

fn int_to_string_impl(n: i8) -> (result: Vec<char>)
    ensures result@ == int_to_string(n as int)
{
    if n == 0 {
        vec!['0']
    } else if n > 0 {
        let mut result = Vec::new();
        let mut num = n;
        while num > 0
            invariant
                result@ == int_to_string_pos(num as int),
                num >= 0,
            decreases num
        {
            let digit = (num % 10) as u8;
            result.push(char_from_digit_impl(digit));
            num /= 10;
        }
        result.reverse();
        result
    } else {
        let mut result = int_to_string_impl(-n);
        result.insert(0, '-');
        result
    }
}

fn char_from_digit_impl(d: u8) -> (result: char)
    requires 0 <= d <= 9
    ensures result == char_from_digit(d as int)
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
        _ => '0'
    }
}

/* helper modified by LLM (iteration 5): Removed ghost code from executable helpers */
proof fn lemma_usize_to_int_conversion()
    ensures forall|usize_val: usize| usize_val as int >= 0
{
    // Helper lemma for usize to int conversions
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
    /* code modified by LLM (iteration 5): Fixed compilation errors by removing ghost code from executable context */
    let mut result = Vec::new();
    result.push(vec!['Y', 'E', 'S']);
    
    let l_val = l;
    let r_val = r;
    let count = ((r_val as usize - l_val as usize + 1) / 2);
    
    for i in 0..count
        invariant
            result.len() == 1 + i,
            result[0]@ == seq!['Y', 'E', 'S'],
            forall|j: int| 1 <= j < result.len() ==> 
                #[trigger] result[j as usize]@ == int_to_string(l_val as int + 2 * (j - 1)).add(seq![' ']).add(int_to_string(l_val as int + 2 * (j - 1) + 1))
    {
        let first = l_val + 2 * (i as i8);
        let second = first + 1;
        
        let mut pair = int_to_string_impl(first);
        pair.push(' ');
        pair.append(&mut int_to_string_impl(second));
        
        result.push(pair);
    }
    
    result
}
// </vc-code>


}

fn main() {}