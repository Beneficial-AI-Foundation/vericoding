// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    exists|i: int, j: int| 0 <= i < j < input.len() && input[i] == ' ' && input[j] == ' ' &&
    ({
        let parts = split_string_spec(input);
        parts.len() >= 3 && 
        is_valid_integer(parts[0]) && is_valid_integer(parts[1]) && is_valid_integer(parts[2]) &&
        ({
            let a = string_to_int_spec(parts[0]);
            let b = string_to_int_spec(parts[1]);
            let c = string_to_int_spec(parts[2]);
            1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
        })
    })
}

spec fn compute_drinks(a: int, b: int, c: int) -> int {
    if b / a < c { b / a } else { c }
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && s[i] <= '9'
}

spec fn string_to_int_spec(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 1 { 
        s[0] as int - '0' as int
    } else if s.len() > 1 { 
        string_to_int_spec(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] as int - '0' as int)
    } else {
        0
    }
}

spec fn split_string_spec(s: Seq<char>) -> Seq<Seq<char>> {
    if s.len() == 0 { 
        seq![] 
    } else {
        split_helper(s, 0, seq![])
    }
}

spec fn split_helper(s: Seq<char>, index: int, current: Seq<char>) -> Seq<Seq<char>>
    decreases s.len() - index
{
    if index >= s.len() {
        if current.len() > 0 { seq![current] } else { seq![] }
    } else if s[index] == ' ' || s[index] == '\n' || s[index] == '\t' {
        if current.len() > 0 { 
            seq![current] + split_helper(s, index + 1, seq![])
        } else { 
            split_helper(s, index + 1, seq![])
        }
    } else {
        split_helper(s, index + 1, current.push(s[index]))
    }
}

spec fn int_to_string_spec(n: int) -> Seq<char>
    decreases n
{
    if n == 0 { 
        seq!['0'] 
    } else if n < 10 && n > 0 { 
        seq![('0' as int + n) as char]
    } else if n > 0 { 
        int_to_string_spec(n / 10) + seq![('0' as int + (n % 10)) as char]
    } else {
        seq!['0']
    }
}
// </vc-preamble>

// <vc-helpers>
fn split_string(s: Vec<char>) -> Vec<Vec<char>>
    ensures
        result@ == split_string_spec(s@),
{
    if s.len() == 0 {
        Vec::new()
    } else {
        split_helper_exec(s, 0, Vec::new())
    }
}

fn split_helper_exec(s: Vec<char>, index: usize, current: Vec<char>) -> Vec<Vec<char>>
    decreases (s.len() - index) as int
    ensures
        result@ == split_helper(s@, index as int, current@),
{
    if index >= s.len() {
        if current.len() > 0 {
            vec![current]
        } else {
            Vec::new()
        }
    } else if s[index] == ' ' || s[index] == '\n' || s[index] == '\t' {
        if current.len() > 0 {
            let mut res = vec![current];
            res.append(&mut split_helper_exec(s, index + 1, Vec::new()));
            res
        } else {
            split_helper_exec(s, index + 1, Vec::new())
        }
    } else {
        let mut curr = current;
        curr.push(s[index]);
        split_helper_exec(s, index + 1, curr)
    }
}

fn string_to_int(s: Vec<char>) -> int
    requires
        is_valid_integer(s@),
    ensures
        result == string_to_int_spec(s@),
{
    let mut num = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            num == string_to_int_spec(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        num = num * 10 + (s[i] as int - '0' as int);
        i += 1;
    }
    num
}

fn int_to_string(n: int) -> Vec<char>
    requires
        n >= 0,
    ensures
        result@ == int_to_string_spec(n),
{
    if n == 0 {
        vec!['0']
    } else if n < 10 {
        vec![('0' as int + n) as char]
    } else {
        let mut prefix = int_to_string(n / 10);
        prefix.push(('0' as int + (n % 10)) as char);
        prefix
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires
        valid_input(input@),
    ensures
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        ({
            let parts = split_string_spec(input@);
            let a = string_to_int_spec(parts[0]);
            let b = string_to_int_spec(parts[1]);
            let c = string_to_int_spec(parts[2]);
            let drinks = compute_drinks(a, b, c);
            result@ == int_to_string_spec(drinks) + seq!['\n']
        }),
// </vc-spec>
// <vc-code>
{
    let parted = split_string(input);
    let a = string_to_int(parted[0].clone());
    let b = string_to_int(parted[1].clone());
    let c = string_to_int(parted[2].clone());
    let drinks = if b / a < c { b / a } else { c };
    let mut result = int_to_string(drinks);
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}