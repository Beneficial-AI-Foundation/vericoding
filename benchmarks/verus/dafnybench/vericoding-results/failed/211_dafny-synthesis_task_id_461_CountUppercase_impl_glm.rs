use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// <vc-helpers>
proof fn filter_concat_equal<A>(s1: Seq<A>, s2: Seq<A>, p: spec_fn(A) -> bool)
    requires
        forall|i: int| 0 <= i < s1.len() ==> #[trigger] p(s1[i]),
        forall|i: int| 0 <= i < s2.len() ==> #[trigger] p(s2[i]),
    ensures
        s1.filter(p).len() + s2.filter(p).len() == (s1 + s2).filter(p).len()
{
    assert(forall|i: int| #[trigger] ((s1 + s2).filter(p))[i] == 
        if i < s1.filter(p).len() { s1.filter(p)[i] } else { s2.filter(p)[i - s1.filter(p).len()] });
}

proof fn filter_single_char<A>(c: A, p: spec_fn(A) -> bool, result: bool)
    requires
        result == p(c),
    ensures
        Seq::singleton(c).filter(p).len() == (if result { 1 } else { 0 })
{
    assert(forall|i: int| #[trigger] (Seq::singleton(c).filter(p))[i] == (if result && i == 0 { c } else { arbitrary() }));
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
    let mut i: nat = 0;
    let s_seq = s@;
    while i < s_seq.len()
        invariant
            i <= s_seq.len(),
            count as int == s_seq.subrange(0, i as int).filter(|c: char| is_upper_case(c)).len(),
    {
        let char_at_i = s_seq[i];
        if is_upper_case(char_at_i) {
            proof {
                filter_single_char(char_at_i, |c: char| is_upper_case(c), true);
                filter_concat_equal(
                    s_seq.subrange(0, i as int),
                    Seq::singleton(char_at_i),
                    |c: char| is_upper_case(c),
                );
            }
            count += 1;
        } else {
            proof {
                filter_single_char(char_at_i, |c: char| is_upper_case(c), false);
                filter_concat_equal(
                    s_seq.subrange(0, i as int),
                    Seq::singleton(char_at_i),
                    |c: char| is_upper_case(c),
                );
            }
        }
        i += 1;
    }
    count
}
// </vc-code>

fn main() {}

}