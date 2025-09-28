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
fn string_from_seq(s: Seq<char>) -> (result: String)
    ensures result@ == s
{
    let mut res = String::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            res@ == s.subrange(0, i as int),
    {
        res.push(s[i]);
        i += 1;
    }
    res
}

fn int_to_string_exec(n: i32) -> (result: String)
    ensures result@ == int_to_string(n as int)
{
    if n < 0 {
        let mut res = String::new();
        res.push('-');
        let pos_str = int_to_string_pos_exec((-n) as u32);
        res.push_str(&pos_str);
        res
    } else {
        int_to_string_pos_exec(n as u32)
    }
}

fn int_to_string_pos_exec(n: u32) -> (result: String)
    ensures result@ == int_to_string_pos(n as nat)
    decreases n
{
    if n < 10 {
        let mut res = String::new();
        res.push(((n as u8) + b'0') as char);
        res
    } else {
        let mut res = int_to_string_pos_exec(n / 10);
        let last_digit = int_to_string_pos_exec(n % 10);
        res.push_str(&last_digit);
        res
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<String>)
    requires n as int >= 2
    ensures valid_output(n as int, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ghost type usage in sequence indexing */
    let mut result = Vec::new();
    
    if n < 6 {
        result.push(string_from_seq(seq!['-', '1']));
        let mut i: i8 = 1;
        while i < n
            invariant
                2 <= n < 6,
                1 <= i <= n,
                result.len() == i as int,
                result[0]@ == seq!['-', '1'],
                forall|j: int| #![auto] 1 <= j < i ==> result[j]@ == seq!['1', ' '] + int_to_string(j + 2),
        {
            let ghost s = seq!['1', ' '] + int_to_string(i as int + 2);
            result.push(string_from_seq(s));
            i += 1;
        }
    } else {
        result.push(string_from_seq(seq!['1', ' ', '2']));
        result.push(string_from_seq(seq!['1', ' ', '3']));
        result.push(string_from_seq(seq!['1', ' ', '4']));
        result.push(string_from_seq(seq!['2', ' ', '5']));
        result.push(string_from_seq(seq!['2', ' ', '6']));
        
        let mut i: i8 = 5;
        while i < 5 + (n - 6)
            invariant
                n >= 6,
                5 <= i <= 5 + (n - 6),
                result.len() == i as int,
                result[0]@ == seq!['1', ' ', '2'],
                result[1]@ == seq!['1', ' ', '3'],
                result[2]@ == seq!['1', ' ', '4'],
                result[3]@ == seq!['2', ' ', '5'],
                result[4]@ == seq!['2', ' ', '6'],
                forall|j: int| #![auto] 5 <= j < i ==> result[j]@ == seq!['1', ' '] + int_to_string(j + 2),
        {
            let ghost s = seq!['1', ' '] + int_to_string(i as int + 2);
            result.push(string_from_seq(s));
            i += 1;
        }
        
        let mut j: i8 = 0;
        while j < n - 1
            invariant
                n >= 6,
                0 <= j <= n - 1,
                result.len() == (5 + (n - 6)) + j as int,
                result[0]@ == seq!['1', ' ', '2'],
                result[1]@ == seq!['1', ' ', '3'],
                result[2]@ == seq!['1', ' ', '4'],
                result[3]@ == seq!['2', ' ', '5'],
                result[4]@ == seq!['2', ' ', '6'],
                forall|k: int| #![auto] 5 <= k < 5 + (n - 6) ==> result[k]@ == seq!['1', ' '] + int_to_string(k + 2),
                forall|k: int| #![auto] 5 + (n - 6) <= k < result.len() ==> result[k]@ == seq!['1', ' '] + int_to_string(k - (5 + (n - 6)) + 2),
        {
            let ghost s = seq!['1', ' '] + int_to_string(j as int + 2);
            result.push(string_from_seq(s));
            j += 1;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}