// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(p: int) -> bool {
    2 <= p < 2000
}

spec fn count_primitive_roots(p: int) -> int
    recommends valid_input(p)
{
    if p == 2 { 
        1 
    } else { 
        /* Count of integers i where 1 <= i < p-1 and 
           for all j where 2 <= j <= i, not ((p-1) % j == 0 && i % j == 0) */
        Set::new(|i: int| 1 <= i < p-1 && (forall|j: int| 2 <= j <= i ==> !((p-1) % j == 0 && #[trigger] (i % j) == 0))).len() as int
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define property prop for gcd-like condition */
spec fn prop(q: int, i: int) -> bool {
    forall|j: int| 2 <= j <= i ==> !((q % j == 0) && ((i % j) == 0))
}

/* helper modified by LLM (iteration 5): extend forall one step when previous range holds and next point holds */
proof fn lemma_extend_forall_no_div(q: int, i: int, m: int)
    requires
        m >= 1,
        forall|k: int| 2 <= k <= m ==> !(q % k == 0 && i % k == 0),
        !(q % (m + 1) == 0 && i % (m + 1) == 0),
    ensures
        forall|k: int| 2 <= k <= m + 1 ==> !(q % k == 0 && i % k == 0),
{
    assert forall |k: int|
        2 <= k <= m + 1 ==> !(q % k == 0 && i % k == 0) by {
        if 2 <= k && k <= m {
            assert(!(q % k == 0 && i % k == 0));
        } else {
            assert(k == m + 1);
            assert(!(q % k == 0 && i % k == 0));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(p: i8) -> (result: i8)
    requires valid_input(p as int)
    ensures 
        result >= 0 &&
        result as int == count_primitive_roots(p as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use exec integers only in executable code and mirror spec with ghost values */
    let n: i32 = p as i32;
    if n == 2 {
        return 1i8;
    }

    let q_exec: i32 = n - 1;
    let ghost q: int = (p as int) - 1;

    let mut total: i32 = 0;
    let ghost mut s: Set<int> = Set::empty();

    let mut i: i32 = 1;
    while i < q_exec
        invariant
            1 <= i as int <= q,
            q == q_exec as int,
            0 <= total,
            s == Set::new(|x: int| 1 <= x < i as int && prop(q, x)),
            total as int == s.len() as int,
        decreases q - i as int
    {
        let mut ok: bool = true;
        let mut j: i32 = 2;
        while j <= i
            invariant
                2 <= j as int <= (i as int) + 1,
                ok == (forall|k: int| 2 <= k < j as int ==> !(q % k == 0 && (i as int) % k == 0)),
            decreases (i as int) - j as int + 1
        {
            if q_exec % j == 0 && i % j == 0 {
                ok = false;
            } else {
                proof {
                    if ok {
                        let ghost jj: int = j as int;
                        lemma_extend_forall_no_div(q, i as int, jj - 1);
                    }
                }
            }
            j += 1;
        }

        proof {
            assert(ok == prop(q, i as int));
        }

        if ok {
            total += 1;
            proof {
                assert(!s.contains(i as int));
                s = s.insert(i as int);
            }
        }

        proof {
            assert(s == Set::new(|x: int| 1 <= x < (i as int) + 1 && prop(q, x)));
        }

        i += 1;
    }

    let res: i8 = total as i8;
    res
}
// </vc-code>


}

fn main() {}