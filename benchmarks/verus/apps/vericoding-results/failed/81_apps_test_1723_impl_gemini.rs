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
/* helper modified by LLM (iteration 5): fixed call to the correct UTF8 lemma from vstd::bytes */
fn int_to_string_pos_exec(n: u32) -> (s: String)
    ensures s@ == int_to_string_pos(n as nat),
    decreases n
{
    if n < 10 {
        let mut v = Vec::new();
        v.push(n as u8 + b'0');
        proof {
            vstd::bytes::lemma_ascii_is_valid_utf8(v@);
        }
        String::from_utf8(v).unwrap()
    } else {
        let s1 = int_to_string_pos_exec(n / 10);
        let s2 = int_to_string_pos_exec(n % 10);
        s1.concat(s2)
    }
}

fn int_to_string_exec(n: i32) -> (s: String)
    ensures s@ == int_to_string(n as int)
{
    if n < 0 {
        let s_pos = int_to_string_pos_exec((-n) as u32);
        String::from_str("-").concat(s_pos)
    } else {
        int_to_string_pos_exec(n as u32)
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
    /* code modified by LLM (iteration 5): no changes, the primary error was a compile error in the helpers */
    let ghost n_int = n as int;
    let n32 = n as i32;
    let mut result: Vec<String> = Vec::new();

    if n32 < 6 {
        result.push(String::from_str("-1"));

        let mut i: i32 = 1;
        while i < n32
            invariant
                n_int == n32 as int,
                2 <= n_int < 6,
                1 <= i <= n32,
                result.len() == i as nat,
                result[0]@ == seq!['-', '1'],
                forall|j: int| 1 <= j < i as int ==> result[j]@ == seq!['1', ' '] + int_to_string(j + 1),
            decreases n32 - i
        {
            let to_print = i + 1;
            let s_num = int_to_string_exec(to_print);
            let s = String::from_str("1 ").concat(s_num);
            result.push(s);
            i = i + 1;
        }
    } else {
        result.push(String::from_str("1 2"));
        result.push(String::from_str("1 3"));
        result.push(String::from_str("1 4"));
        result.push(String::from_str("2 5"));
        result.push(String::from_str("2 6"));

        let mut i_loop1: i32 = 5;
        let end1: i32 = n32 - 1;
        while i_loop1 < end1
            invariant
                n_int == n32 as int,
                n_int >= 6,
                end1 == n32 - 1,
                5 <= i_loop1 <= end1,
                result.len() == i_loop1 as nat,
                result[0]@ == seq!['1', ' ', '2'],
                result[1]@ == seq!['1', ' ', '3'],
                result[2]@ == seq!['1', ' ', '4'],
                result[3]@ == seq!['2', ' ', '5'],
                result[4]@ == seq!['2', ' ', '6'],
                forall|j: int| 5 <= j < i_loop1 as int ==> result[j]@ == seq!['1', ' '] + int_to_string(j + 2),
            decreases end1 - i_loop1
        {
            let to_print = i_loop1 + 2;
            let s_num = int_to_string_exec(to_print);
            let s = String::from_str("1 ").concat(s_num);
            result.push(s);
            i_loop1 = i_loop1 + 1;
        }

        let mut i_loop2: i32 = n32 - 1;
        let end2: i32 = 2 * n32 - 2;
        while i_loop2 < end2
            invariant
                n_int == n32 as int,
                n_int >= 6,
                end1 == n32 - 1,
                end2 == 2 * n32 - 2,
                (n32 - 1) <= i_loop2 <= end2,
                result.len() == i_loop2 as nat,
                result[0]@ == seq!['1', ' ', '2'],
                result[1]@ == seq!['1', ' ', '3'],
                result[2]@ == seq!['1', ' ', '4'],
                result[3]@ == seq!['2', ' ', '5'],
                result[4]@ == seq!['2', ' ', '6'],
                forall|j: int| 5 <= j < end1 as int ==> result[j]@ == seq!['1', ' '] + int_to_string(j + 2),
                forall|j: int| end1 as int <= j < i_loop2 as int ==> result[j]@ == seq!['1', ' '] + int_to_string(j - (end1 as int) + 2),
            decreases end2 - i_loop2
        {
            let to_print = i_loop2 - (n32 - 1) + 2;
            let s_num = int_to_string_exec(to_print);
            let s = String::from_str("1 ").concat(s_num);
            result.push(s);
            i_loop2 = i_loop2 + 1;
        }
    }
    result
}
// </vc-code>


}

fn main() {}