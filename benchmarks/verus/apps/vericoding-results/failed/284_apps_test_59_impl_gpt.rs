// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>, p: Seq<char>) -> bool {
    n >= 2 &&
    a.len() == n &&
    p.len() == n - 1 &&
    (forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i] == '0' || #[trigger] p[i] == '1') &&
    (forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= n) &&
    a.to_set() =~= Set::new(|i: int| 1 <= i <= n)
}

spec fn max_up_to(a: Seq<int>, i: int) -> int
    recommends 0 <= i < a.len()
    decreases i when i >= 0
{
    if i == 0 { 
        a[0] 
    } else if i > 0 && a[i] > max_up_to(a, i-1) { 
        a[i] 
    } else if i > 0 { 
        max_up_to(a, i-1) 
    } else {
        a[0]
    }
}

spec fn can_sort(n: int, a: Seq<int>, p: Seq<char>) -> bool
    recommends valid_input(n, a, p)
{
    forall|i: int| 0 <= i < n - 1 ==> 
        (#[trigger] p[i] == '0' ==> max_up_to(a, i) <= i + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): step lemma for max_up_to recurrence */
proof fn lemma_max_up_to_step(a: Seq<int>, i: int)
    requires
        0 <= i < a.len() - 1,
    ensures
        max_up_to(a, i + 1) == if a[i + 1] > max_up_to(a, i) { a[i + 1] } else { max_up_to(a, i) },
{
    assert(max_up_to(a, i + 1) == if i + 1 == 0 { a[0] } else if i + 1 > 0 && a[i + 1] > max_up_to(a, i) { a[i + 1] } else if i + 1 > 0 { max_up_to(a, i) } else { a[0] });
}

/* helper modified by LLM (iteration 2): constructor for "YES" string */
fn make_yes() -> (res: String)
    ensures
        res@ == seq!['Y', 'E', 'S'],
{
    let mut s = String::new();
    s.push('Y');
    s.push('E');
    s.push('S');
    s
}

/* helper modified by LLM (iteration 2): constructor for "NO" string */
fn make_no() -> (res: String)
    ensures
        res@ == seq!['N', 'O'],
{
    let mut s = String::new();
    s.push('N');
    s.push('O');
    s
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>, p: Vec<char>) -> (result: String)
    requires
        valid_input(n as int, a@.map(|i, x| x as int), p@),
    ensures
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        (result@ == seq!['Y', 'E', 'S']) <==> can_sort(n as int, a@.map(|i, x| x as int), p@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use exec types for computation and ghost/spec reasoning for proofs and invariants */
    let len_a_usize: usize = a.len();
    let len_p_usize: usize = p.len();

    proof {
        assert(valid_input(n as int, a@.map(|i, x| x as int), p@));
        assert(len_a_usize as int == n as int);
        assert(len_p_usize as int == n as int - 1);
    }

    let mut i: usize = 0;
    let mut m: i32 = a[0] as i32;
    let mut ok: bool = true;

    while i < len_p_usize
        invariant
            0 <= i as int <= len_p_usize as int,
            i as int < len_a_usize as int,
            (m as int) == max_up_to(a@.map(|j, x| x as int), i as int),
            ok == (forall|k: int| 0 <= k < i as int ==> (p@[k] == '0' ==> max_up_to(a@.map(|t, x| x as int), k) <= k + 1)),
        decreases (len_p_usize as int) - (i as int)
    {
        let j = i;
        let ch = p[j];
        let cond_j = if ch == '0' { m <= (j as i32) + 1 } else { true };
        let prev_ok = ok;
        ok = prev_ok && cond_j;

        if j + 1 < len_a_usize {
            let ai1 = a[j + 1] as i32;
            proof { lemma_max_up_to_step(a@.map(|t, x| x as int), j as int); }
            if ai1 > m {
                m = ai1;
            }
        }

        i = j + 1;

        proof {
            assert(cond_j == (p@[j as int] == '0' ==> max_up_to(a@.map(|t, x| x as int), j as int) <= j as int + 1));
            assert(prev_ok == (forall|k: int| 0 <= k < j as int ==> (p@[k] == '0' ==> max_up_to(a@.map(|t, x| x as int), k) <= k + 1)));
            assert((forall|k: int| 0 <= k < j as int + 1 ==> (p@[k] == '0' ==> max_up_to(a@.map(|t, x| x as int), k) <= k + 1))
                == (((forall|k: int| 0 <= k < j as int ==> (p@[k] == '0' ==> max_up_to(a@.map(|t, x| x as int), k) <= k + 1))
                    && (p@[j as int] == '0' ==> max_up_to(a@.map(|t, x| x as int), j as int) <= j as int + 1))));
            assert(ok == (forall|k: int| 0 <= k < i as int ==> (p@[k] == '0' ==> max_up_to(a@.map(|t, x| x as int), k) <= k + 1)));
        }
    }

    let res = if ok { make_yes() } else { make_no() };

    proof {
        assert(ok == (forall|k: int| 0 <= k < len_p_usize as int ==> (p@[k] == '0' ==> max_up_to(a@.map(|t, x| x as int), k) <= k + 1)));
        assert(len_p_usize as int == n as int - 1);
        assert(can_sort(n as int, a@.map(|t, x| x as int), p@)
            == (forall|k: int| 0 <= k < n as int - 1 ==> (p@[k] == '0' ==> max_up_to(a@.map(|t, x| x as int), k) <= k + 1)));
    }

    res
}
// </vc-code>


}

fn main() {}