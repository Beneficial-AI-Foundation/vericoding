// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3 && s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
}

spec fn valid_abbreviation(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() >= 3 &&
    s.len() >= 3 &&
    result[0] == s[0] &&
    result[result.len() - 1] == s[s.len() - 1] &&
    result == seq![s[0]].add(int_to_string(s.len() - 2)).add(seq![s[s.len() - 1]])
}

spec fn int_to_string(n: int) -> Seq<char>
    decreases if n >= 0 { n } else { -n }
{
    if n == 0 {
        seq!['0']
    } else if n < 0 {
        seq!['-'].add(int_to_string_helper(-n))
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n <= 0 {
        Seq::new(0 as nat, |_i: int| ' ')
    } else {
        int_to_string_helper(n / 10).add(seq![(('0' as int) + (n % 10)) as char])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `seq_to_vec_char` helper had a compilation error because `s[i as int]` attempts to use Verus `int` in an executable context. This was fixed by using a `ghost` variable `i_nat` to correctly index the sequence with a `nat` type while still iterating with `i` as the executable `usize` index. */

fn seq_to_vec_char(s: Seq<char>) -> (v: Vec<char>)
    ensures
        v@ == s,
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i as int <= s.len() as int,
            v@ == s.subsequence(0, i as int),
    {
        // Need to use a ghost variable to access the sequence with nat index, 
        // as `s[i]` expects a nat, and `i` is usize which can be converted to int.
        // `i_nat` is a ghost variable to satisfy verus's type system
        let i_nat: nat = i as nat;
        v.push(s[i_nat]);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_abbreviation(s@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error where `int_to_string` was called with a native type `usize` that was then cast to `int`. This is resolved by ensuring the input to `int_to_string` is explicitly an `int` type from the start, as it expects, and only converting to `usize` for executable code. */
{
    let first_char = s[0];
    let last_char = s[s.len() - 1];
    let middle_num_val: int = s.len() as int - 2;

    let middle_str_spec = int_to_string(middle_num_val);

    let middle_str_vec = seq_to_vec_char(middle_str_spec);

    let mut result_vec = Vec::new();
    result_vec.push(first_char);

    let mut k: usize = 0;
    while k < middle_str_vec.len()
        invariant
            0 <= k as int <= middle_str_vec.len() as int,
            result_vec@ == seq![first_char].add(middle_str_vec@.subsequence(0, k as int)),
    {
        result_vec.push(middle_str_vec[k]);
        k = k + 1;
    }
    
    result_vec.push(last_char);

    proof {
        assert(result_vec@ == seq![first_char].add(middle_str_vec@).add(seq![last_char]));
        assert(middle_str_vec@ == middle_str_spec);
        assert(result_vec@ == seq![first_char].add(middle_str_spec).add(seq![last_char]));
        assert(s.len() >= 3);
        assert(valid_abbreviation(s@, result_vec@));
    }

    result_vec
}
// </vc-code>


}

fn main() {}