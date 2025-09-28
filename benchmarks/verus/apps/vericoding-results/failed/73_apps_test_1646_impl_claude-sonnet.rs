// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_binary_string(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1') &&
    (s == seq!['0'] || s[0] == '1')
}

spec fn count_zeros(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0int
    } else { 
        (if s[0] == '0' { 1int } else { 0int }) + count_zeros(s.subrange(1, s.len() as int))
    }
}

spec fn create_zero_seq(n: nat) -> Seq<char> {
    Seq::new(n, |i: int| '0')
}

spec fn is_minimal_form(s: Seq<char>, result: Seq<char>) -> bool {
    (s == seq!['0'] ==> result == seq!['0'])
    &&
    (s != seq!['0'] ==> result == seq!['1'] + create_zero_seq(count_zeros(s) as nat))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed nat type usage in executable code */
fn count_zeros_create_zero_seq(n: nat)
    ensures count_zeros(create_zero_seq(n)) == n as int
    decreases n
{
    if n == 0 {
    } else {
        count_zeros_create_zero_seq(n - 1);
    }
}

fn count_zeros_cons(c: char, s: Seq<char>)
    ensures count_zeros(seq![c] + s) == (if c == '0' { 1int } else { 0int }) + count_zeros(s)
{
}

fn valid_binary_string_concat(s1: Seq<char>, s2: Seq<char>)
    requires
        s1.len() > 0,
        forall|i: int| 0 <= i < s1.len() ==> s1[i] == '0' || s1[i] == '1',
        forall|i: int| 0 <= i < s2.len() ==> s2[i] == '0' || s2[i] == '1',
        s1[0] == '1',
    ensures
        valid_binary_string(s1 + s2)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, s: Vec<char>) -> (result: Vec<char>)
    requires 
        n >= 1 && n <= 100,
        s.len() == n as usize,
        valid_binary_string(s@),
    ensures 
        valid_binary_string(result@),
        is_minimal_form(s@, result@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed, only helpers were fixed */
    if s@ == seq!['0'] {
        vec!['0']
    } else {
        let mut zero_count: u8 = 0;
        let mut i: usize = 0;
        
        while i < s.len()
            invariant
                i <= s.len(),
                zero_count <= 100,
                count_zeros(s@.subrange(0, i as int)) == zero_count as int,
        {
            if s[i] == '0' {
                zero_count = zero_count + 1;
            }
            i = i + 1;
        }
        
        proof {
            assert(s@.subrange(0, s.len() as int) == s@);
        }
        
        let mut result = vec!['1'];
        let mut j: usize = 0;
        
        while j < zero_count as usize
            invariant
                j <= zero_count as usize,
                result.len() == j + 1,
                result@[0] == '1',
                forall|k: int| 1 <= k < result.len() ==> result@[k] == '0',
                result@ == seq!['1'] + create_zero_seq(j as nat),
        {
            result.push('0');
            j = j + 1;
        }
        
        proof {
            count_zeros_create_zero_seq(zero_count as nat);
        }
        
        result
    }
}
// </vc-code>


}

fn main() {}