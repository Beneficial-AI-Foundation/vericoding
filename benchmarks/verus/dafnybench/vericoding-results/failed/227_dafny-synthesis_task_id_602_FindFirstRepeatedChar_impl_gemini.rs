// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn no_repeats_upto(s: Seq<char>, n: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < n ==> s[i] != s[j]
}

/* helper modified by LLM (iteration 4): [fixed compilation error by changing 'implies' to '==>'] */
proof fn lemma_no_repeats_extend(s: Seq<char>, j: int)
    requires
        0 <= j < s.len(),
        no_repeats_upto(s, j),
        forall|k: int| 0 <= k < j ==> s[k] != s[j],
    ensures
        no_repeats_upto(s, j + 1),
{
    forall|i1: int, i2: int| 0 <= i1 < i2 < j + 1 ==> s[i1] != s[i2]
    by {
        if i2 < j {
            assert(no_repeats_upto(s, j));
        } else {
            assert(i2 == j);
            assert(forall|k: int| 0 <= k < j ==> s[k] != s[j]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures 
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 && 
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [no significant changes, logic appears correct after fixing helper compilation] */
    let s_vec: Vec<char> = s.chars().collect();
    let s_seq = s_vec@;
    vstd::string::lemma_collect_chars_spec(s);

    let mut j: usize = 0;
    while j < s_vec.len()
        invariant
            0 <= j <= s_vec.len(),
            s_vec@ == s@,
            no_repeats_upto(s_seq, j as int),
        decreases s_vec.len() - j
    {
        let current_char = s_vec[j];
        let mut i: usize = 0;
        while i < j
            invariant
                0 <= i <= j,
                j < s_vec.len(),
                s_vec@ == s@,
                no_repeats_upto(s_seq, j as int),
                forall|k: int| 0 <= k < i as int ==> s_seq[k] != s_seq[j as int],
            decreases j - i
        {
            if s_vec[i] == current_char {
                return (true, current_char);
            }
            i = i + 1;
        }

        assert(no_repeats_upto(s_seq, (j + 1) as int)) by {
            lemma_no_repeats_extend(s_seq, j as int);
        }

        j = j + 1;
    }
    
    return (false, '\0');
}
// </vc-code>

}
fn main() {}