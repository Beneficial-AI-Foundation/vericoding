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
proof fn lemma_int_to_string_pos_valid(n: nat)
    ensures
        int_to_string_pos(n).len() > 0,
        forall|i: int| 0 <= i < int_to_string_pos(n).len() ==> ('0' as int <= int_to_string_pos(n)[i] as int <= '9' as int),
    decreases n
{
    if n < 10 {
        assert(int_to_string_pos(n).len() == 1);
        assert(int_to_string_pos(n)[0] as int == ('0' as nat + n) as int);
        assert(('0' as nat + n) as int <= '9' as int);
    } else {
        lemma_int_to_string_pos_valid(n / 10);
        lemma_int_to_string_pos_valid(n % 10);
        assert(int_to_string_pos(n).len() == int_to_string_pos(n / 10).len() + int_to_string_pos(n % 10).len());
        assert(int_to_string_pos(n / 10).len() > 0);
        assert(int_to_string_pos(n % 10).len() > 0);
    }
}

proof fn lemma_int_to_string_valid(n: int)
    ensures
        int_to_string(n).len() > 0,
        if n < 0 {
            int_to_string(n)[0] == '-'
        } else {
            forall|i: int| 0 <= i < int_to_string(n).len() ==> ('0' as int <= int_to_string(n)[i] as int <= '9' as int)
        },
    decreases if n < 0 { -n } else { n }
{
    if n < 0 {
        let pos_n = (-n) as nat;
        lemma_int_to_string_pos_valid(pos_n);
        assert(int_to_string(n)[0] == '-');
        assert(int_to_string(n).len() == 1 + int_to_string_pos(pos_n).len());
    } else {
        lemma_int_to_string_pos_valid(n as nat);
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
    /* code modified by LLM (iteration 3): Fixed type comparison error by using proper sequence comparison */
    let mut result = Vec::new();
    
    if n < 6 {
        result.push("-1".to_string());
        let mut i = 1;
        while i < n as usize
            invariant
                result@.len() == i,
                result@[0] == seq!['-', '1'],
                forall|j: int| 1 <= j < i ==> result@[j] == seq!['1', ' '] + int_to_string(j + 1),
                i <= n as int,
        {
            let num = i + 1;
            let s = format!("1 {}", num);
            result.push(s);
            i += 1;
        }
    } else {
        result.push("1 2".to_string());
        result.push("1 3".to_string());
        result.push("1 4".to_string());
        result.push("2 5".to_string());
        result.push("2 6".to_string());
        
        let mut i = 5;
        while i < 5 + (n - 6) as usize
            invariant
                result@.len() == i,
                result@[0] == seq!['1', ' ', '2'],
                result@[1] == seq!['1', ' ', '3'],
                result@[2] == seq!['1', ' ', '4'],
                result@[3] == seq!['2', ' ', '5'],
                result@[4] == seq!['2', ' ', '6'],
                forall|j: int| 5 <= j < i ==> result@[j] == seq!['1', ' '] + int_to_string(j + 2),
                i <= 5 + (n - 6) as int,
        {
            let num = i + 2;
            let s = format!("1 {}", num);
            result.push(s);
            i += 1;
        }
        
        let mut i = 5 + (n - 6) as usize;
        while i < 5 + (n - 6) as usize + (n - 1) as usize
            invariant
                result@.len() == i,
                forall|j: int| 5 + (n - 6) as int <= j < i ==> result@[j] == seq!['1', ' '] + int_to_string(j - (5 + (n - 6) as int) + 2),
                i <= 5 + (n - 6) as int + (n - 1) as int,
        {
            let offset = i - (5 + (n - 6) as usize);
            let num = offset + 2;
            let s = format!("1 {}", num);
            result.push(s);
            i += 1;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}