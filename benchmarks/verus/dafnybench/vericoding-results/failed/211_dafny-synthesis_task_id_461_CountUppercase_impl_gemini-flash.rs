use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// <vc-helpers>
#[verifier(external_body)]
#[cfg(test)]
pub fn str_to_seq_char(s: &str) -> Seq<char> {
    s.chars().collect::<Vec<char>>().into()
}

// Helper function to get a subsequence of a vector
pub open spec fn vec_subsequence<T>(s: &Seq<T>, start: int, end: int) -> Seq<T>
    recommends 0 <= start <= end <= s.len() as int
{
    Seq::new((end - start) as nat, |j: int| s.index(start + j))
}
// </vc-helpers>

// <vc-spec>
fn count_uppercase(s: &str) -> (count: usize)
    ensures 
        count >= 0,
        count as int == s@.filter(|c: char| is_upper_case(c)).len(),
// </vc-spec>
// <vc-code>
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    let s_chars = s.chars().collect::<Vec<char>>();
    let s_char_seq = Seq::new(s_chars.len() as nat, |k: nat| s_chars[k]);

    #[verifier(loop_invariant)]
    #[verifier(decreases_by (s_chars.len() as int) - (i as int))]
    while i < s_chars.len()
        invariant
            count as int == vec_subsequence(&s_char_seq, 0, i as int).filter(|c: char| is_upper_case(c)).len(),
            i <= s_chars.len(),
            count >= 0,
    {
        let c = s_chars[i];
        if is_upper_case(c) {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>

fn main() {}

}