// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_output(n: int, result: Seq<String>) -> bool
    recommends n >= 2
{
    if n < 6 {
        result.len() == 1 + (n - 1) &&
        result[0]@ == seq!['-', '1'] &&
        (forall|i: int| #![auto] 1 <= i < result.len() ==> result[i]@ == seq!['1', ' '] + int_to_string(i + 1))
    } else {
        result.len() == (5 + (n - 6)) + (n - 1) &&
        result[0]@ == seq!['1', ' ', '2'] && 
        result[1]@ == seq!['1', ' ', '3'] && 
        result[2]@ == seq!['1', ' ', '4'] && 
        result[3]@ == seq!['2', ' ', '5'] && 
        result[4]@ == seq!['2', ' ', '6'] &&
        (forall|i: int| #![auto] 5 <= i < 5 + (n - 6) ==> result[i]@ == seq!['1', ' '] + int_to_string(i + 2)) &&
        (forall|i: int| #![auto] 5 + (n - 6) <= i < result.len() ==> result[i]@ == seq!['1', ' '] + int_to_string(i - (5 + (n - 6)) + 2))
    }
}

spec fn int_to_string_pos(n: nat) -> Seq<char>
    decreases n
{
    if n < 10 {
        seq![(n + ('0' as nat)) as char]
    } else {
        int_to_string_pos(n / 10) + int_to_string_pos(n % 10)
    }
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n < 0 {
        seq!['-'] + int_to_string_pos((-n) as nat)
    } else {
        int_to_string_pos(n as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that casting i8 to int preserves ordering */
proof fn i8_cast_preserves_order(a: i8, b: i8)
    requires
        a <= b,
    ensures
        (a as int) <= (b as int),
{
    assert((a as int) <= (b as int));
}

/* helper modified by LLM (iteration 5): runtime integer to decimal String conversion */
fn int_to_string_runtime(mut n: i8) -> String {
    // Build the characters into a Vec<char>, then convert to a String
    if n == 0 {
        return String::from("0");
    }
    let mut neg = false;
    if n < 0 {
        neg = true;
        n = -n;
    }
    let mut digits: Vec<char> = Vec::new();
    while n > 0
        invariant
            n >= 0,
        decreases (n as int)
    {
        let d = (n % 10) as u8;
        digits.push((('0' as u8) + d) as char);
        n = n / 10;
    }
    let mut s = if neg { String::from("-") } else { String::from("") };
    while !digits.is_empty()
        invariant
            true,
        decreases (digits.len() as int)
    {
        let ch = digits.pop().unwrap();
        s.push(ch);
    }
    s
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<String>)
    requires n as int >= 2
    ensures valid_output(n as int, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement solve using String::from for initial strings and int_to_string_runtime helper */
    let mut res: Vec<String> = Vec::new();
    let n8: i8 = n;
    if n8 < 6 {
        res.push(String::from("-1"));
        let mut i: i8 = 1;
        while i < n8
            invariant
                1 <= i,
            decreases (n8 - i)
        {
            let s = String::from("1 ") + &int_to_string_runtime(i + 1);
            res.push(s);
            i += 1;
        }
    } else {
        res.push(String::from("1 2"));
        res.push(String::from("1 3"));
        res.push(String::from("1 4"));
        res.push(String::from("2 5"));
        res.push(String::from("2 6"));
        let mut i: i8 = 5;
        while i < (n8 - 1)
            invariant
                5 <= i,
            decreases ((n8 - 1) - i)
        {
            let val = i + 2;
            let s = String::from("1 ") + &int_to_string_runtime(val);
            res.push(s);
            i += 1;
        }
        let mut j: i8 = n8 - 1;
        while j < (2 * n8 - 2)
            invariant
                n8 - 1 <= j,
            decreases ((2 * n8 - 2) - j)
        {
            let val = j - (n8 - 1) + 2;
            let s = String::from("1 ") + &int_to_string_runtime(val);
            res.push(s);
            j += 1;
        }
    }
    res
}

// </vc-code>


}

fn main() {}