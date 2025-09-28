// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int) -> bool {
    1 <= r <= 100
}

spec fn dodecagon_area(r: int) -> int {
    3 * r * r
}

spec fn int_to_string(n: int) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string(n / 10) + int_to_string(n % 10)
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 1 {
        (s[0] as int) - ('0' as int)
    } else if s.len() > 1 {
        string_to_int(s.subrange(0, s.len() - 1)) * 10 + ((s[s.len() - 1] as int) - ('0' as int))
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversions and sequence indexing */
spec fn int_to_string_injective_lemma(n: int, m: int)
    requires
        int_to_string(n) =~= int_to_string(m),
    ensures
        n == m,
    decreases n + m
{
    if n == 0 && m == 0 {
    } else if n < 10 && m < 10 {
        assert((int_to_string(n) =~= seq![('0' as int + n) as char]) && (int_to_string(m) =~= seq![('0' as int + m) as char]));
        assert(('0' as int + n) as char == ('0' as int + m) as char);
        assert(n == m);
    } else if n >= 10 && m >= 10 {
        assert(int_to_string(n) =~= int_to_string(n / 10) + int_to_string(n % 10));
        assert(int_to_string(m) =~= int_to_string(m / 10) + int_to_string(m % 10));
        let sn = int_to_string(n);
        let sm = int_to_string(m);
        assert(sn.len() == sm.len());
        assert(sn.subrange(0, sn.len() - 1) =~= sm.subrange(0, sm.len() - 1));
        assert(sn[sn.len() - 1] == sm[sm.len() - 1]);
        int_to_string_injective_lemma(n / 10, m / 10);
        int_to_string_injective_lemma(n % 10, m % 10);
        assert(n % 10 == m % 10);
        assert(n / 10 == m / 10);
        assert(n == (n / 10) * 10 + (n % 10));
        assert(m == (m / 10) * 10 + (m % 10));
    } else {
        let sn = int_to_string(n);
        let sm = int_to_string(m);
        assert(sn.len() >= 1 && sm.len() >= 1);
        if n < 10 {
            assert(sn.len() == 1);
            assert(sm.len() > 1);
        } else {
            assert(sm.len() == 1);
            assert(sn.len() > 1);
        }
        assert(false);
    }
}

spec fn string_to_int_correct_lemma(s: Seq<char>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> ('0' as int) <= (s[i] as int) <= ('9' as int),
    ensures
        string_to_int(s) >= 0,
        int_to_string(string_to_int(s)) =~= s,
    decreases s.len()
{
    if s.len() == 1 {
        let n = string_to_int(s);
        assert(n == (s[0] as int) - ('0' as int));
        assert(int_to_string(n) =~= seq![('0' as int + n) as char]);
        assert(('0' as int + n) as char == ('0' as int + ((s[0] as int) - ('0' as int))) as char);
        assert(('0' as int + ((s[0] as int) - ('0' as int))) as char == s[0]);
    } else {
        let s_prefix = s.subrange(0, s.len() - 1);
        let last_char = s[s.len() - 1];
        string_to_int_correct_lemma(s_prefix);
        let prefix_val = string_to_int(s_prefix);
        let last_digit = (last_char as int) - ('0' as int);
        assert(string_to_int(s) == prefix_val * 10 + last_digit);
        assert(int_to_string(string_to_int(s)) =~= int_to_string(prefix_val * 10 + last_digit));
        assert(int_to_string(prefix_val * 10 + last_digit) =~= int_to_string(prefix_val * 10) + int_to_string(last_digit));
        assert(int_to_string(prefix_val * 10) =~= int_to_string(prefix_val) + int_to_string(0));
        assert(int_to_string(0) =~= seq!['0']);
        assert(int_to_string(last_digit) =~= seq![('0' as int + last_digit) as char]);
        assert(('0' as int + last_digit) as char == last_char);
        assert(int_to_string(prefix_val) =~= s_prefix);
    }
}

spec fn valid_input_string(s: Seq<char>) -> bool {
    s.len() > 0
    && forall|i: int| 0 <= i < s.len() ==> ('0' as int) <= (s[i] as int) <= ('9' as int)
    && valid_input(string_to_int(s))
}

spec fn r_from_string(s: Seq<char>) -> int {
    string_to_int(s)
}

spec fn area_from_r(r: int) -> int {
    dodecagon_area(r)
}

spec fn output_string(area: int) -> Seq<char> {
    int_to_string(area)
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches and sequence indexing */
{
    let input_seq = stdin_input@;
    proof {
        assert(input_seq.len() > 0);
        assert(forall|i: int| 0 <= i < input_seq.len() ==> ('0' as int) <= (input_seq[i] as int) <= ('9' as int));
        assert(valid_input(r_from_string(input_seq)));
    }
    
    let r_value = string_to_int(input_seq);
    let area_value = area_from_r(r_value);
    let output_seq = int_to_string(area_value);
    
    let mut result = String::new();
    let mut i: usize = 0;
    while i < output_seq.len() as usize
        invariant
            0 <= i <= output_seq.len(),
            result@ =~= output_seq.subrange(0, i),
    {
        result.push(output_seq[i] as char);
        i = i + 1;
    }
    
    assert(result@ =~= output_string(r_from_string(input_seq)));
    (result)
}
// </vc-code>


}

fn main() {}