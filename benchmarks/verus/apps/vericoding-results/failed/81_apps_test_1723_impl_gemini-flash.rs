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
/* helper modified by LLM (iteration 4): Removed unused spec function. */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<String>)
    requires n as int >= 2
    ensures valid_output(n as int, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Changed `n_int` to be a ghost variable. */
    let ghost n_int = n as int;
    let mut result: Vec<String> = Vec::new();

    if n_int < 6 {
        result.push(String::from("-1"));
        let mut i: i8 = 1;
        while (i as int) < n_int
            invariant
                1 <= (i as int),
                (i as int) <= n_int,
                result@.len() == (i as int),
                result[0]@ == seq!['-', '1'],
                (forall|k: int| #![auto] 1 <= k < (i as int) ==> result[k]@ == seq!['1', ' '] + int_to_string(k + 1))
            decreases n_int - (i as int)
        {
            let s = String::from("1 ") + (i + 1).to_string();
            result.push(s);
            i = i + 1;
        }
    } else {
        result.push(String::from("1 2"));
        result.push(String::from("1 3"));
        result.push(String::from("1 4"));
        result.push(String::from("2 5"));
        result.push(String::from("2 6"));

        let mut i: i8 = 5;
        while (i as int) < n_int
            invariant
                5 <= (i as int),
                (i as int) <= n_int,
                result@.len() == (i as int),
                result[0]@ == seq!['1', ' ', '2'],
                result[1]@ == seq!['1', ' ', '3'],
                result[2]@ == seq!['1', ' ', '4'],
                result[3]@ == seq!['2', ' ', '5'],
                result[4]@ == seq!['2', ' ', '6'],
                (forall|k: int| #![auto] 5 <= k < (i as int) ==> result[k]@ == seq!['1', ' '] + int_to_string(k + 2))
            decreases n_int - (i as int)
        {
            let s = String::from("1 ") + (i + 2).to_string();
            result.push(s);
            i = i + 1;
        }

        let mut i: i8 = 0;
        while (i as int) < n_int - 1
            invariant
                (i as int) >= 0,
                (i as int) <= n_int - 1,
                result@.len() == 5 + (n_int - 6) + (i as int),
                result[0]@ == seq!['1', ' ', '2'],
                result[1]@ == seq!['1', ' ', '3'],
                result[2]@ == seq!['1', ' ', '4'],
                result[3]@ == seq!['2', ' ', '5'],
                result[4]@ == seq!['2', ' ', '6'],
                (forall|k: int| #![auto] 5 <= k < 5 + (n_int - 6) ==> result[k]@ == seq!['1', ' '] + int_to_string(k + 2)),
                (forall|k: int| #![auto] 5 + (n_int - 6) <= k < 5 + (n_int - 6) + (i as int) ==> result[k]@ == seq!['1', ' '] + int_to_string(k - (5 + (n_int - 6)) + 2))
            decreases (n_int - 1) - (i as int)
        {
            let s = String::from("1 ") + (i + 2).to_string();
            result.push(s);
            i = i + 1;
        }
    }

    result
}
// </vc-code>


}

fn main() {}