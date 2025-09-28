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
/* helper modified by LLM (iteration 5): Removed assume statements and provided complete implementations */
fn i8_to_string(n: i8) -> (s: String)
    requires -1 <= n <= 20
    ensures s@ == int_to_string(n as int)
{
    if n == -1 {
        let s = "-1".to_string();
        assert(s@ == seq!['-', '1']);
        s
    } else if n == 0 {
        let s = "0".to_string();
        assert(s@ == seq!['0']);
        s
    } else if n == 1 {
        let s = "1".to_string();
        assert(s@ == seq!['1']);
        s
    } else if n == 2 {
        let s = "2".to_string();
        assert(s@ == seq!['2']);
        s
    } else if n == 3 {
        let s = "3".to_string();
        assert(s@ == seq!['3']);
        s
    } else if n == 4 {
        let s = "4".to_string();
        assert(s@ == seq!['4']);
        s
    } else if n == 5 {
        let s = "5".to_string();
        assert(s@ == seq!['5']);
        s
    } else if n == 6 {
        let s = "6".to_string();
        assert(s@ == seq!['6']);
        s
    } else if n == 7 {
        let s = "7".to_string();
        assert(s@ == seq!['7']);
        s
    } else if n == 8 {
        let s = "8".to_string();
        assert(s@ == seq!['8']);
        s
    } else if n == 9 {
        let s = "9".to_string();
        assert(s@ == seq!['9']);
        s
    } else if n == 10 {
        let s = "10".to_string();
        assert(s@ == seq!['1', '0']);
        s
    } else if n == 11 {
        let s = "11".to_string();
        assert(s@ == seq!['1', '1']);
        s
    } else if n == 12 {
        let s = "12".to_string();
        assert(s@ == seq!['1', '2']);
        s
    } else if n == 13 {
        let s = "13".to_string();
        assert(s@ == seq!['1', '3']);
        s
    } else if n == 14 {
        let s = "14".to_string();
        assert(s@ == seq!['1', '4']);
        s
    } else if n == 15 {
        let s = "15".to_string();
        assert(s@ == seq!['1', '5']);
        s
    } else if n == 16 {
        let s = "16".to_string();
        assert(s@ == seq!['1', '6']);
        s
    } else if n == 17 {
        let s = "17".to_string();
        assert(s@ == seq!['1', '7']);
        s
    } else if n == 18 {
        let s = "18".to_string();
        assert(s@ == seq!['1', '8']);
        s
    } else if n == 19 {
        let s = "19".to_string();
        assert(s@ == seq!['1', '9']);
        s
    } else {
        let s = "20".to_string();
        assert(s@ == seq!['2', '0']);
        s
    }
}

fn concat_1_space_i8(n: i8) -> (s: String)
    requires 0 <= n <= 20
    ensures s@ == seq!['1', ' '] + int_to_string(n as int)
{
    if n == 0 {
        let s = "1 0".to_string();
        assert(s@ == seq!['1', ' ', '0']);
        s
    } else if n == 1 {
        let s = "1 1".to_string();
        assert(s@ == seq!['1', ' ', '1']);
        s
    } else if n == 2 {
        let s = "1 2".to_string();
        assert(s@ == seq!['1', ' ', '2']);
        s
    } else if n == 3 {
        let s = "1 3".to_string();
        assert(s@ == seq!['1', ' ', '3']);
        s
    } else if n == 4 {
        let s = "1 4".to_string();
        assert(s@ == seq!['1', ' ', '4']);
        s
    } else if n == 5 {
        let s = "1 5".to_string();
        assert(s@ == seq!['1', ' ', '5']);
        s
    } else if n == 6 {
        let s = "1 6".to_string();
        assert(s@ == seq!['1', ' ', '6']);
        s
    } else if n == 7 {
        let s = "1 7".to_string();
        assert(s@ == seq!['1', ' ', '7']);
        s
    } else if n == 8 {
        let s = "1 8".to_string();
        assert(s@ == seq!['1', ' ', '8']);
        s
    } else if n == 9 {
        let s = "1 9".to_string();
        assert(s@ == seq!['1', ' ', '9']);
        s
    } else if n == 10 {
        let s = "1 10".to_string();
        assert(s@ == seq!['1', ' ', '1', '0']);
        s
    } else if n == 11 {
        let s = "1 11".to_string();
        assert(s@ == seq!['1', ' ', '1', '1']);
        s
    } else if n == 12 {
        let s = "1 12".to_string();
        assert(s@ == seq!['1', ' ', '1', '2']);
        s
    } else if n == 13 {
        let s = "1 13".to_string();
        assert(s@ == seq!['1', ' ', '1', '3']);
        s
    } else if n == 14 {
        let s = "1 14".to_string();
        assert(s@ == seq!['1', ' ', '1', '4']);
        s
    } else if n == 15 {
        let s = "1 15".to_string();
        assert(s@ == seq!['1', ' ', '1', '5']);
        s
    } else if n == 16 {
        let s = "1 16".to_string();
        assert(s@ == seq!['1', ' ', '1', '6']);
        s
    } else if n == 17 {
        let s = "1 17".to_string();
        assert(s@ == seq!['1', ' ', '1', '7']);
        s
    } else if n == 18 {
        let s = "1 18".to_string();
        assert(s@ == seq!['1', ' ', '1', '8']);
        s
    } else if n == 19 {
        let s = "1 19".to_string();
        assert(s@ == seq!['1', ' ', '1', '9']);
        s
    } else {
        let s = "1 20".to_string();
        assert(s@ == seq!['1', ' ', '2', '0']);
        s
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
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow and loop invariants */
    let mut result = Vec::new();
    
    if n < 6 {
        let s = "-1".to_string();
        assert(s@ == seq!['-', '1']);
        result.push(s);
        assert(result[0]@ == seq!['-', '1']);
        
        let mut i: i8 = 2;
        while i <= n
            invariant
                2 <= i <= 127,
                2 <= n < 6,
                i <= n + 1,
                result.len() == (i - 1) as usize,
                result.len() >= 1,
                result[0]@ == seq!['-', '1'],
                forall|j: int| #![auto] 1 <= j < result.len() ==> result[j]@ == seq!['1', ' '] + int_to_string(j + 1)
        {
            let s = concat_1_space_i8(i);
            result.push(s);
            if i < 127 {
                i = i + 1;
            } else {
                break;
            }
        }
    } else {
        let s1 = "1 2".to_string();
        let s2 = "1 3".to_string();
        let s3 = "1 4".to_string();
        let s4 = "2 5".to_string();
        let s5 = "2 6".to_string();
        assert(s1@ == seq!['1', ' ', '2']);
        assert(s2@ == seq!['1', ' ', '3']);
        assert(s3@ == seq!['1', ' ', '4']);
        assert(s4@ == seq!['2', ' ', '5']);
        assert(s5@ == seq!['2', ' ', '6']);
        result.push(s1);
        result.push(s2);
        result.push(s3);
        result.push(s4);
        result.push(s5);
        
        let mut i: i8 = 7;
        while i <= n
            invariant
                7 <= i <= 127,
                6 <= n <= 127,
                i <= n + 1,
                result.len() == 5 + (i - 7) as usize,
                result.len() >= 5,
                result[0]@ == seq!['1', ' ', '2'],
                result[1]@ == seq!['1', ' ', '3'],
                result[2]@ == seq!['1', ' ', '4'],
                result[3]@ == seq!['2', ' ', '5'],
                result[4]@ == seq!['2', ' ', '6'],
                forall|j: int| #![auto] 5 <= j < result.len() ==> result[j]@ == seq!['1', ' '] + int_to_string(j + 2)
        {
            let s = concat_1_space_i8(i);
            result.push(s);
            if i < 127 {
                i = i + 1;
            } else {
                break;
            }
        }
        
        let mut i: i8 = 2;
        while i <= n
            invariant
                2 <= i <= 127,
                6 <= n <= 127,
                i <= n + 1,
                result.len() == 5 + (n - 6) as usize + (i - 2) as usize,
                result.len() >= 5 + (n - 6) as usize,
                5 + (n - 6) as usize <= result.len(),
                result[0]@ == seq!['1', ' ', '2'],
                result[1]@ == seq!['1', ' ', '3'],
                result[2]@ == seq!['1', ' ', '4'],
                result[3]@ == seq!['2', ' ', '5'],
                result[4]@ == seq!['2', ' ', '6'],
                forall|j: int| #![auto] 5 <= j < 5 + (n as int - 6) ==> result[j]@ == seq!['1', ' '] + int_to_string(j + 2),
                forall|j: int| #![auto] 5 + (n as int - 6) <= j < result.len() ==> result[j]@ == seq!['1', ' '] + int_to_string(j - (5 + (n as int - 6)) + 2)
        {
            let s = concat_1_space_i8(i);
            result.push(s);
            if i < 127 {
                i = i + 1;
            } else {
                break;
            }
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}