// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn monotonic(l: Seq<int>) -> bool {
    if l.len() <= 1 {
        true
    } else {
        let increasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] <= l[(i + 1) as int];
        let decreasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] >= l[(i + 1) as int];
        increasing || decreasing
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): refine extension lemmas and clean indexing to support loop invariants */
proof fn lemma_forall_extend_le(s: Seq<int>, i: nat)
    requires
        i + 1 < s.len(),
    ensures
        (forall|j: nat| #![trigger s[j as int]] j < i + 1 ==> s[j as int] <= s[(j + 1) as int])
        == ((forall|j: nat| #![trigger s[j as int]] j < i ==> s[j as int] <= s[(j + 1) as int]) && s[i as int] <= s[(i + 1) as int]),
{
    assert(((forall|j: nat| #![trigger s[j as int]] j < i + 1 ==> s[j as int] <= s[(j + 1) as int]))
        ==> ((forall|j: nat| #![trigger s[j as int]] j < i ==> s[j as int] <= s[(j + 1) as int]) && s[i as int] <= s[(i + 1) as int])) by {
        assert forall|j: nat| #![trigger s[j as int]] j < i implies s[j as int] <= s[(j + 1) as int] by {
            assert(j < i + 1);
        }
        assert(s[i as int] <= s[(i + 1) as int]) by {
            assert(i < i + 1);
        }
    }
    assert((((forall|j: nat| #![trigger s[j as int]] j < i ==> s[j as int] <= s[(j + 1) as int]) && s[i as int] <= s[(i + 1) as int]))
        ==> (forall|j: nat| #![trigger s[j as int]] j < i + 1 ==> s[j as int] <= s[(j + 1) as int])) by {
        assert forall|j: nat| #![trigger s[j as int]] j < i + 1 implies s[j as int] <= s[(j + 1) as int] by {
            if j < i {
                assert(s[j as int] <= s[(j + 1) as int]);
            } else {
                assert(j == i);
                assert(s[i as int] <= s[(i + 1) as int]);
            }
        }
    }
}

/* helper modified by LLM (iteration 5): refine extension lemmas and clean indexing to support loop invariants */
proof fn lemma_forall_extend_ge(s: Seq<int>, i: nat)
    requires
        i + 1 < s.len(),
    ensures
        (forall|j: nat| #![trigger s[j as int]] j < i + 1 ==> s[j as int] >= s[(j + 1) as int])
        == ((forall|j: nat| #![trigger s[j as int]] j < i ==> s[j as int] >= s[(j + 1) as int]) && s[i as int] >= s[(i + 1) as int]),
{
    assert(((forall|j: nat| #![trigger s[j as int]] j < i + 1 ==> s[j as int] >= s[(j + 1) as int]))
        ==> ((forall|j: nat| #![trigger s[j as int]] j < i ==> s[j as int] >= s[(j + 1) as int]) && s[i as int] >= s[(i + 1) as int])) by {
        assert forall|j: nat| #![trigger s[j as int]] j < i implies s[j as int] >= s[(j + 1) as int] by {
            assert(j < i + 1);
        }
        assert(s[i as int] >= s[(i + 1) as int]) by {
            assert(i < i + 1);
        }
    }
    assert((((forall|j: nat| #![trigger s[j as int]] j < i ==> s[j as int] >= s[(j + 1) as int]) && s[i as int] >= s[(i + 1) as int]))
        ==> (forall|j: nat| #![trigger s[j as int]] j < i + 1 ==> s[j as int] >= s[(j + 1) as int])) by {
        assert forall|j: nat| #![trigger s[j as int]] j < i + 1 implies s[j as int] >= s[(j + 1) as int] by {
            if j < i {
                assert(s[j as int] >= s[(j + 1) as int]);
            } else {
                assert(j == i);
                assert(s[i as int] >= s[(i + 1) as int]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_monotonic(l: Vec<i8>) -> (result: bool)
    ensures result == monotonic(l@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): declare ghost sequence for spec-level ints and use it in loop invariants and proofs */
    if l.len() <= 1 {
        proof {
            let s = l@.map(|_i: int, x: i8| x as int);
            assert(s.len() <= 1);
            assert(monotonic(s));
        }
        true
    } else {
        let ghost s = l@.map(|_i: int, x: i8| x as int);
        let mut i: usize = 0;
        let mut inc: bool = true;
        let mut dec: bool = true;
        while i + 1 < l.len()
            invariant
                0 <= i as int,
                i as int <= l.len() as int - 1,
                s.len() == l.len() as int,
                inc == (forall|j: nat| #![trigger s[j as int]] j < i as nat ==> s[j as int] <= s[(j + 1) as int]),
                dec == (forall|j: nat| #![trigger s[j as int]] j < i as nat ==> s[j as int] >= s[(j + 1) as int]),
            decreases l.len() as int - 1 - i as int
        {
            let a: i8 = l[i];
            let b: i8 = l[i + 1];
            inc = inc && (a <= b);
            dec = dec && (a >= b);
            proof {
                assert(((i as int) + 1) < s.len());
                assert((i as int) < s.len());
                assert(s[i as int] == (l@[i as int] as int));
                assert(s[(i + 1) as int] == (l@[(i + 1) as int] as int));
                assert(l@[i as int] == a);
                assert(l@[(i + 1) as int] == b);
                if a <= b {
                    assert((a as int) <= (b as int));
                    assert(s[i as int] <= s[(i + 1) as int]);
                }
                if a >= b {
                    assert((a as int) >= (b as int));
                    assert(s[i as int] >= s[(i + 1) as int]);
                }
                assert((i as nat) + 1 < s.len());
                lemma_forall_extend_le(s, i as nat);
                lemma_forall_extend_ge(s, i as nat);
            }
            i = i + 1;
        }
        let res = inc || dec;
        proof {
            assert(i as int == l.len() as int - 1);
            assert(s.len() == l.len() as int);

            let inc_prop = (forall|j: nat| #![trigger s[j as int]] j < i as nat ==> s[j as int] <= s[(j + 1) as int]);
            let dec_prop = (forall|j: nat| #![trigger s[j as int]] j < i as nat ==> s[j as int] >= s[(j + 1) as int]);
            assert(inc == inc_prop);
            assert(dec == dec_prop);

            let increasing = (forall|j: nat| #![trigger s[j as int]] j < s.len() - 1 ==> s[j as int] <= s[(j + 1) as int]);
            let decreasing = (forall|j: nat| #![trigger s[j as int]] j < s.len() - 1 ==> s[j as int] >= s[(j + 1) as int]);

            assert(inc ==> increasing) by {
                if inc {
                    assert(inc_prop);
                    assert forall|j: nat| #![trigger s[j as int]] j < s.len() - 1 implies s[j as int] <= s[(j + 1) as int] by {
                        assert(j < i as nat) by { assert(i as int == s.len() - 1); }
                        assert(s[j as int] <= s[(j + 1) as int]);
                    }
                }
            }
            assert(increasing ==> inc) by {
                if increasing {
                    assert forall|j: nat| #![trigger s[j as int]] j < i as nat implies s[j as int] <= s[(j + 1) as int] by {
                        assert(j < s.len() - 1);
                        assert(j < i as nat) by { assert(i as int == s.len() - 1); }
                    }
                    assert(inc_prop);
                }
            }
            assert(dec ==> decreasing) by {
                if dec {
                    assert(dec_prop);
                    assert forall|j: nat| #![trigger s[j as int]] j < s.len() - 1 implies s[j as int] >= s[(j + 1) as int] by {
                        assert(j < i as nat) by { assert(i as int == s.len() - 1); }
                        assert(s[j as int] >= s[(j + 1) as int]);
                    }
                }
            }
            assert(decreasing ==> dec) by {
                if decreasing {
                    assert forall|j: nat| #![trigger s[j as int]] j < i as nat implies s[j as int] >= s[(j + 1) as int] by {
                        assert(j < s.len() - 1);
                        assert(j < i as nat) by { assert(i as int == s.len() - 1); }
                    }
                    assert(dec_prop);
                }
            }
            assert((inc || dec) == (increasing || decreasing));
            assert(monotonic(s) == (increasing || decreasing));
            assert(res == monotonic(s));
        }
        res
    }
}
// </vc-code>


}

fn main() {}