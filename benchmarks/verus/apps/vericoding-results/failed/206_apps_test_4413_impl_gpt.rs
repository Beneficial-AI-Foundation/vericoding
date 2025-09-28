// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(skills: Seq<int>) -> bool {
    skills.len() >= 0
}

spec fn has_adjacent_skills(skills: Seq<int>) -> bool {
    exists|i: int, j: int| 0 <= i < j < skills.len() && (skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate capturing absolute difference of 1 between two integers */
spec fn diff1(x: int, y: int) -> bool {
    x - y == 1 || y - x == 1
}
// </vc-helpers>

// <vc-spec>
fn solve(skills: Vec<i8>) -> (teams: i8)
    requires 
        valid_input(skills@.map(|i, x| x as int))
    ensures 
        teams == 1 || teams == 2,
        teams == 2 <==> has_adjacent_skills(skills@.map(|i, x| x as int)),
        teams == 1 <==> !has_adjacent_skills(skills@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): tightened invariants and parenthesized casts to fix parsing, plus proof relating found to spec */
    let n: usize = skills.len();
    let s = skills@.map(|k, x| x as int);
    proof { assert(s.len() == n as int); }

    let mut found: bool = false;
    let mut i: usize = 0;
    while i < n
        invariant
            (0 <= i as int),
            (i as int) <= (n as int),
            s.len() == (n as int),
            found ==> has_adjacent_skills(s),
            !found ==> forall|p: int, q: int|
                0 <= p && p < (i as int) && p < q && q < (n as int)
                ==> !diff1(s[p], s[q])
        decreases (n as int) - (i as int)
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                (0 <= i as int),
                (i as int) < (n as int),
                (0 <= j as int),
                (j as int) <= (n as int),
                (j as int) >= (i as int) + 1,
                s.len() == (n as int),
                found ==> has_adjacent_skills(s),
                !found ==> forall|q: int|
                    (i as int) < q && q < (j as int)
                    ==> !diff1(s[i as int], s[q])
            decreases (n as int) - (j as int)
        {
            let xi: i8 = skills[i];
            let xj: i8 = skills[j];
            let xi_int: int = xi as int;
            let xj_int: int = xj as int;
            let old_j: usize = j;

            if xi_int - xj_int == 1 || xj_int - xi_int == 1 {
                proof {
                    let p = i as int;
                    let q = j as int;
                    assert(0 <= p && p < q && q < s.len());
                    assert(skills@[p] == skills[i]);
                    assert(skills@[q] == skills[j]);
                    assert(s[p] == (skills@[p]) as int);
                    assert(s[q] == (skills@[q]) as int);
                    assert(s[p] - s[q] == 1 || s[q] - s[p] == 1);
                    assert(exists|pp: int, qq: int|
                        0 <= pp && pp < qq && qq < s.len() &&
                        (s[pp] - s[qq] == 1 || s[qq] - s[pp] == 1)) by {
                        let pp = p; let qq = q;
                        assert(0 <= pp && pp < qq && qq < s.len());
                        assert(s[pp] - s[qq] == 1 || s[qq] - s[pp] == 1);
                    }
                    assert(has_adjacent_skills(s));
                }
                found = true;
            }

            j = j + 1;

            if !found {
                proof {
                    assert(forall|q: int|
                        (i as int) < q && q < (j as int)
                        ==> !diff1(s[i as int], s[q])) by {
                        if (i as int) < q && q < (j as int) {
                            if q < old_j as int {
                                // holds from previous invariant
                            } else {
                                assert(q == old_j as int);
                                let p = i as int;
                                let q0 = old_j as int;
                                assert(0 <= p && p < n as int);
                                assert(0 <= q0 && q0 < n as int);
                                assert(skills@[p] == skills[i]);
                                assert(skills@[q0] == skills[old_j]);
                                assert(s[p] == (skills@[p]) as int);
                                assert(s[q0] == (skills@[q0]) as int);
                                assert(!(xi_int - xj_int == 1 || xj_int - xi_int == 1));
                                assert(!diff1(s[p], s[q0]));
                            }
                        }
                    }
                }
            }
        }

        if !found {
            proof {
                assert(forall|q: int| (i as int) < q && q < (n as int) ==> !diff1(s[i as int], s[q]));
            }
        }

        if !found {
            proof {
                assert(forall|p: int, q: int|
                    0 <= p && p < (i as int) + 1 && p < q && q < (n as int)
                    ==> !diff1(s[p], s[q])) by {
                    if 0 <= p && p < (i as int) + 1 && p < q && q < (n as int) {
                        if p < (i as int) {
                            assert(!diff1(s[p], s[q]));
                        } else {
                            assert(p == i as int);
                            assert(!diff1(s[p], s[q]));
                        }
                    }
                }
            }
        }

        i = i + 1;
    }

    proof {
        let n_int = s.len();
        assert(n_int == n as int);
        if !found {
            assert(forall|p: int, q: int| 0 <= p && p < q && q < n_int ==> !diff1(s[p], s[q]));
            assert(!has_adjacent_skills(s));
        } else {
            assert(has_adjacent_skills(s));
        }
    }

    if found { 2i8 } else { 1i8 }
}
// </vc-code>


}

fn main() {}