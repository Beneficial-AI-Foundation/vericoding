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
spec fn expected_pair(l: int, k: int) -> Seq<char> {
    int_to_string(l + 2 * k).add(seq![' ']).add(int_to_string(l + 2 * k + 1))
}

fn char_from_digit_exec(d: i64) -> (c: char)
    requires
        0 <= d,
        d <= 9,
    ensures
        c == char_from_digit(d as int),
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

fn int_to_string_pos_exec(n: i64) -> (v: Vec<char>)
    requires
        n > 0,
    ensures
        v@ == int_to_string_pos(n as int),
    decreases n as int
{
    if n < 10 {
        let mut v: Vec<char> = Vec::new();
        let c = char_from_digit_exec(n);
        v.push(c);
        v
    } else {
        let mut v = int_to_string_pos_exec(n / 10);
        let c = char_from_digit_exec(n % 10);
        v.push(c);
        v
    }
}

fn int_to_string_exec(n: i64) -> (v: Vec<char>)
    ensures
        v@ == int_to_string(n as int),
{
    if n == 0 {
        let mut v: Vec<char> = Vec::new();
        v.push('0');
        v
    } else if n > 0 {
        int_to_string_pos_exec(n)
    } else {
        let mut v: Vec<char> = Vec::new();
        v.push('-');
        let t = int_to_string_pos_exec(-n);
        append_all(&mut v, &t);
        v
    }
}

/* helper modified by LLM (iteration 2): fixed misuse of old() on immutable reference; preserved src without old() */
fn append_all(dst: &mut Vec<char>, src: &Vec<char>)
    ensures
        dst@ == old(dst)@.add(src@),
{
    let mut i: usize = 0;
    while i < src.len()
        invariant
            0 <= i as int,
            i as int <= src.len() as int,
            dst@ == old(dst)@.add(src@.subrange(0, i as int)),
        decreases (src.len() - i) as int
    {
        let c = src[i];
        dst.push(c);
        i = i + 1;
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
    /* code modified by LLM (iteration 2): implement construction of YES header and consecutive coprime pairs */
    let mut result: Vec<Vec<char>> = Vec::new();

    let mut yes: Vec<char> = Vec::new();
    yes.push('Y');
    yes.push('E');
    yes.push('S');
    result.push(yes);

    let mut a: i64 = l as i64;
    let end: i64 = r as i64 + 1;

    while a < end
        invariant
            result.len() >= 1,
            result[0]@ == seq!['Y', 'E', 'S'],
            result.len() == 1 + ((a as int - l as int) / 2),
            forall|k: int| 0 <= k && k < ((a as int - l as int) / 2) ==> #[trigger] result[1 + k]@ == expected_pair(l as int, k),
            a as int <= r as int + 1,
            (a as int - l as int) % 2 == 0,
        decreases (end as int - a as int) / 2
    {
        let b: i64 = a + 1;

        let mut v = int_to_string_exec(a);
        v.push(' ');
        let vb = int_to_string_exec(b);
        append_all(&mut v, &vb);

        result.push(v);
        a = a + 2;
    }

    result
}
// </vc-code>


}

fn main() {}