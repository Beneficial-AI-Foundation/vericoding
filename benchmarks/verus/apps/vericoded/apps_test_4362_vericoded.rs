// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_lowercase_letter(c: char) -> bool {
    'a' <= c && c <= 'z'
}

spec fn all_lowercase(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_lowercase_letter(s[i])
}

spec fn valid_output(result: Seq<char>) -> bool {
    result =~= seq!['A'] || result =~= seq!['a']
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): prove that existence of a non-lowercase character implies not all_lowercase */
proof fn lemma_exists_not_lower_implies_not_all(s: Seq<char>, j: int)
    requires
        0 <= j < s.len(),
        !is_lowercase_letter(s[j]),
    ensures
        !all_lowercase(s),
{
    assert(s.len() > 0);
    assert(!forall|i: int| 0 <= i < s.len() ==> is_lowercase_letter(s[i])) by {
        assert(0 <= j < s.len());
        assert(!is_lowercase_letter(s[j]));
        assert(!(0 <= j < s.len() ==> is_lowercase_letter(s[j])));
    }
    assert(!all_lowercase(s));
}

/* helper modified by LLM (iteration 4): executable checker for all_lowercase with matching spec */
fn check_all_lowercase(v: &Vec<char>) -> (r: bool)
    ensures
        r == all_lowercase(v@),
{
    let mut i: usize = 0;
    let mut ok: bool = true;
    let mut bad: bool = false;
    while i < v.len()
        invariant
            i <= v.len(),
            ok ==> !bad,
            ok ==> forall|j: int| 0 <= j < i as int ==> is_lowercase_letter(v@[j]),
            bad ==> exists|j: int| 0 <= j < i as int && !is_lowercase_letter(v@[j]),
            ok || bad,
        decreases v.len() - i
    {
        let c = v[i];
        let is_lower = c >= 'a' && c <= 'z';
        if !is_lower {
            ok = false;
        }
        bad = bad || !is_lower;
        i += 1;
        proof {
            if ok {
                assert forall|j: int| 0 <= j < i as int ==> is_lowercase_letter(v@[j]) by {
                    let j = j;
                    if j == (i as int) - 1 {
                        assert(v@[(i as int) - 1] == c);
                        assert(is_lower);
                        assert(is_lowercase_letter(v@[(i as int) - 1]));
                    } else if 0 <= j && j < (i as int) - 1 {
                        assert(is_lowercase_letter(v@[j]));
                    }
                }
            }
            if bad && !is_lower {
                assert(0 <= (i as int) - 1);
                assert(((i as int) - 1) < i as int);
                assert(v@[(i as int) - 1] == c);
                assert(!is_lowercase_letter(v@[(i as int) - 1]));
                assert(exists|j: int| 0 <= j < i as int && !is_lowercase_letter(v@[j])) by {
                    let j_w = (i as int) - 1;
                    assert(0 <= j_w && j_w < i as int);
                    assert(!is_lowercase_letter(v@[j_w]));
                }
            }
        }
    }
    let r = if v.len() == 0 { false } else { ok };
    proof {
        if r {
            assert(v.len() > 0);
            assert forall|j: int| 0 <= j < v@.len() ==> is_lowercase_letter(v@[j]) by {
                let j = j;
                if 0 <= j && j < v@.len() {
                    assert(0 <= j < i as int);
                    assert(is_lowercase_letter(v@[j]));
                }
            }
            assert(all_lowercase(v@));
        } else {
            if v.len() == 0 {
                assert(!all_lowercase(v@));
            } else {
                assert(!ok);
                assert(ok || bad);
                assert(bad);
                assert(exists|j: int| 0 <= j < v@.len() && !is_lowercase_letter(v@[j]));
                let j = choose|j: int| 0 <= j < v@.len() && !is_lowercase_letter(v@[j]);
                lemma_exists_not_lower_implies_not_all(v@, j);
                assert(!all_lowercase(v@));
            }
        }
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    ensures 
        valid_output(result@) &&
        (all_lowercase(input@) ==> result@ =~= seq!['a']) &&
        ((input@.len() == 0 || !all_lowercase(input@)) ==> result@ =~= seq!['A'])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): replace Seq->Vec conversion with vec! literal and branch on checker result */
    let r = check_all_lowercase(&input);
    if r {
        vec!['a']
    } else {
        vec!['A']
    }
}
// </vc-code>


}

fn main() {}