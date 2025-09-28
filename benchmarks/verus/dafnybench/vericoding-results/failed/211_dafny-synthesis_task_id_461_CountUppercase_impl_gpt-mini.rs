use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// <vc-helpers>
fn is_upper_case_impl(c: char) -> bool {
    (c as int) >= 65 && (c as int) <= 90
}

proof fn is_upper_case_agree(c: char) {
    assert(is_upper_case(c) == is_upper_case_impl(c));
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
    while i < (s@).len()
        invariant i <= (s@).len(),
        invariant (count as int) == (s@).slice(0, i).filter(|ch: char| is_upper_case_impl(ch)).len(),
        decreases (s@).len() - i
    {
        let c: char = (s@)[i];
        if is_upper_case_impl(c) {
            count += 1;
        }
        proof {
            if is_upper_case_impl(c) {
                assert((s@).slice(0, i+1).filter(|ch: char| is_upper_case_impl(ch)).len()
                    == (s@).slice(0, i).filter(|ch: char| is_upper_case_impl(ch)).len() + 1);
            } else {
                assert((s@).slice(0, i+1).filter(|ch: char| is_upper_case_impl(ch)).len()
                    == (s@).slice(0, i).filter(|ch: char| is_upper_case_impl(ch)).len());
            }
        }
        i += 1;
    }
    assert(i == (s@).len());
    proof {
        assert((count as int) == (s@).slice(0, i).filter(|ch: char| is_upper_case_impl(ch)).len());

        let mut j: nat = 0;
        while j < (s@).len()
            invariant j <= (s@).len(),
            invariant (s@).slice(0, j).filter(|ch: char| is_upper_case(ch)).len()
                == (s@).slice(0, j).filter(|ch: char| is_upper_case_impl(ch)).len(),
            decreases (s@).len() - j
        {
            let c = (s@)[j];
            is_upper_case_agree(c);
            if is_upper_case_impl(c) {
                assert((s@).slice(0, j+1).filter(|ch: char| is_upper_case(ch)).len()
                    == (s@).slice(0, j).filter(|ch: char| is_upper_case(ch)).len() + 1);
                assert((s@).slice(0, j+1).filter(|ch: char| is_upper_case_impl(ch)).len()
                    == (s@).slice(0, j).filter(|ch: char| is_upper_case_impl(ch)).len() + 1);
            } else {
                assert((s@).slice(0, j+1).filter(|ch: char| is_upper_case(ch)).len()
                    == (s@).slice(0, j).filter(|ch: char| is_upper_case(ch)).len());
                assert((s@).slice(0, j+1).filter(|ch: char| is_upper_case_impl(ch)).len()
                    == (s@).slice(0, j).filter(|ch: char| is_upper_case_impl(ch)).len());
            }
            j += 1;
        }

        assert((s@).filter(|ch: char| is_upper_case(ch)).len()
            == (s@).filter(|ch: char| is_upper_case_impl(ch)).len());

        assert((count as int) == (s@).filter(|ch: char| is_upper_case(ch)).len());
    }
    count
}
// </vc-code>

fn main() {}

}