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
/* helper modified by LLM (iteration 5): runtime int to Vec<char> conversion */
fn int_to_vec(n: u64) -> Vec<char>
{
    let mut res: Vec<char> = Vec::new();
    if n == 0 {
        res.push('0');
        return res;
    }
    let mut digits: Vec<char> = Vec::new();
    let mut x: u64 = n;
    while x > 0
        invariant
            x <= n,
        decreases x
    {
        let d = ((('0' as u32) + ((x % 10) as u32)) as char);
        digits.push(d);
        x = x / 10;
    }
    let mut i: usize = digits.len();
    while i > 0
        invariant
            i <= digits.len(),
        decreases i
    {
        i = i - 1;
        res.push(digits[i]);
    }
    res
}

/* helper modified by LLM (iteration 5): proof that int_to_vec matches int_to_string_spec */
proof fn int_to_vec_spec_correct(n: int)
    requires
        n >= 0,
    ensures
        int_to_vec(n as u64)@ == int_to_string_spec(n),
{
    if n == 0 {
        assert(int_to_vec(0 as u64)@ == seq!['0']);
        assert(int_to_string_spec(0) == seq!['0']);
    } else if n > 0 && n < 10 {
        assert(int_to_vec(n as u64)@ == seq![('0' as int + n) as char]);
        assert(int_to_string_spec(n) == seq![('0' as int + n) as char]);
    } else {
        // inductive step
        int_to_vec_spec_correct(n / 10);
        assert(int_to_string_spec(n) == int_to_string_spec(n / 10) + seq![('0' as int + (n % 10)) as char]);
        // relate runtime construction to spec by using the inductive hypothesis
        assert(int_to_vec(n as u64)@ == int_to_vec((n / 10) as u64)@ + seq![('0' as int + (n % 10)) as char]);
        assert(int_to_vec((n / 10) as u64)@ == int_to_string_spec(n / 10));
        assert(int_to_vec(n as u64)@ == int_to_string_spec(n));
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
    /* code modified by LLM (iteration 5): build result via runtime int_to_vec to avoid spec indexing */
    let parts = split_string_spec(input@);
    let a = string_to_int_spec(parts@[0]);
    let b = string_to_int_spec(parts@[1]);
    let c = string_to_int_spec(parts@[2]);
    let drinks = compute_drinks(a, b, c);
    let mut res = int_to_vec(drinks as u64);
    res.push('\n');
    proof {
        int_to_vec_spec_correct(drinks);
        assert(res@ == int_to_string_spec(drinks) + seq!['\n']);
    }
    res
}
// </vc-code>


}

fn main() {}