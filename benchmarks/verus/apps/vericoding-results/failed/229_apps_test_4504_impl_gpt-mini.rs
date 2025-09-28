// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_even_string(s: Seq<char>) -> bool {
    s.len() >= 2 && s.len() % 2 == 0 && s.subrange(0, s.len() as int / 2) == s.subrange(s.len() as int / 2, s.len() as int)
}

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 2 && is_even_string(s)
}

spec fn valid_solution(s: Seq<char>, result: int) -> bool {
    2 <= result < s.len() && result % 2 == 0 && is_even_string(s.subrange(0, result))
}

spec fn is_maximal_solution(s: Seq<char>, result: int) -> bool {
    valid_solution(s, result) && 
    forall|k: int| result < k < s.len() && k % 2 == 0 ==> !is_even_string(s.subrange(0, k))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): unfold valid_solution into components */
fn valid_solution_unfold(s: Seq<char>, k: int)
    requires
        valid_solution(s, k),
    ensures
        2 <= k,
        k < s.len(),
        k % 2 == 0,
        is_even_string(s.subrange(0, k)),
{
    proof {
        assert(2 <= k);
        assert(k < s.len());
        assert(k % 2 == 0);
        assert(is_even_string(s.subrange(0, k)));
    }
}

/* helper modified by LLM (iteration 5): relate pointwise equality of halves to is_even_string */
fn halves_eq_implies_is_even(s: Seq<char>, i: int)
    requires
        2 <= i,
        i % 2 == 0,
        i <= s.len(),
        forall|j: int| 0 <= j < i / 2 ==> s@[j] == s@[j + i / 2],
    ensures
        is_even_string(s.subrange(0, i)),
{
    proof {
        // length and evenness facts
        assert(s.subrange(0, i).len() == i);
        assert(i >= 2);
        assert(i % 2 == 0);

        // show elementwise equality of the two halves
        assert(forall|k: int| 0 <= k < i / 2 ==> s.subrange(0, i / 2)@[k] == s.subrange(i / 2, i)@[k]);
        proof {
            // use the assumption that original sequence has matching elements
            assert(forall|k: int| 0 <= k < i / 2 ==> s@[k] == s@[k + i / 2]);
            // relate subrange indexing to original sequence indexing
            assert(forall|k: int| 0 <= k < i / 2 ==> s.subrange(0, i / 2)@[k] == s@[k]);
            assert(forall|k: int| 0 <= k < i / 2 ==> s.subrange(i / 2, i)@[k] == s@[k + i / 2]);
            assert(forall|k: int| 0 <= k < i / 2 ==> s.subrange(0, i / 2)@[k] == s.subrange(i / 2, i)@[k]);
        }

        // lengths of the halves match
        assert(s.subrange(0, i / 2).len() == i / 2);
        assert(s.subrange(i / 2, i).len() == i / 2);
        // conclude halves are equal as sequences
        assert(s.subrange(0, i / 2) == s.subrange(i / 2, i));

        // thus the prefix of length i is an even string
        assert(is_even_string(s.subrange(0, i)));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: usize)
    requires 
        valid_input(s@) &&
        (exists|k: int| valid_solution(s@, k))
    ensures 
        valid_solution(s@, result as int) &&
        is_maximal_solution(s@, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): downward search with invariants linking runtime checks to spec */
{
    let n = s.len();
    let mut i: usize = if n % 2 == 0 { n - 2 } else { n - 1 };

    while i >= 2
        invariant
            i <= n,
            i % 2 == 0,
            exists|k: int| 2 <= k <= i as int && k % 2 == 0 && valid_solution(s@, k),
            forall|k: int| i as int < k < n as int && k % 2 == 0 ==> !is_even_string(s@.subrange(0, k)),
        decreases i
    {
        let half = i / 2;
        let mut ok = true;
        let mut j: usize = 0;
        while j < half
            invariant
                j <= half,
                forall|k: int| 0 <= k < j as int ==> s@@[k] == s@@[k + half as int],
            decreases (half - j)
        {
            if s[j] != s[j + half] {
                ok = false;
                break;
            } else {
                proof {
                    // relate runtime equality to spec-level seq equality for index j
                    assert(s@@[j as int] == s[j]);
                    assert(s@@[j as int + half as int] == s[j + half]);
                    assert(s@@[j as int] == s@@[j as int + half as int]);
                }
                j += 1;
            }
        }

        if ok {
            proof {
                // from inner invariant we know equality holds for all 0..half
                assert(forall|k: int| 0 <= k < half as int ==> s@@[k] == s@@[k + half as int]);
                // connect runtime equality to the spec-level predicate
                halves_eq_implies_is_even(s@, i as int);
                // assemble valid_solution facts
                assert(2 <= i as int);
                assert(i as int < n as int);
                assert(i as int % 2 == 0);
                assert(is_even_string(s@.subrange(0, i as int)));
            }
            return i;
        }

        // current i is not a solution; step down by two and continue
        if i >= 2 {
            i -= 2;
        } else {
            break;
        }
    }

    // Unreachable due to precondition (exists a valid solution); return a default to satisfy type checker
    2
}

// </vc-code>


}

fn main() {}