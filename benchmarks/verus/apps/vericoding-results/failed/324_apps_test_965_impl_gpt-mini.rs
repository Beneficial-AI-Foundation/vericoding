// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, statuses: Seq<char>) -> bool {
    n >= 2 && statuses.len() == n && 
    forall|i: int| 0 <= i < statuses.len() ==> (statuses[i] == 'A' || statuses[i] == 'I' || statuses[i] == 'F')
}

spec fn count_status(statuses: Seq<char>, status: char) -> int {
    seq_count(statuses, status)
}

spec fn seq_count(s: Seq<char>, target: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let rest_count = seq_count(s.drop_first(), target);
        if s[0] == target {
            rest_count + 1
        } else {
            rest_count
        }
    }
}

spec fn expected_result(statuses: Seq<char>) -> int {
    let cnt_i = count_status(statuses, 'I');
    let cnt_a = count_status(statuses, 'A');
    if cnt_i == 0 { cnt_a }
    else if cnt_i == 1 { 1 }
    else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): counts prefix occurrences of target in a sequence */
spec fn seq_count_prefix(s: Seq<char>, len: int, target: char) -> int
    requires
        0 <= len && len <= s.len(),
    decreases
        len
{
    if len == 0 {
        0
    } else {
        let rest = seq_count_prefix(s.drop_first(), len - 1, target);
        if s[0] == target { rest + 1 } else { rest }
    }
}

/* helper modified by LLM (iteration 4): lemma showing full-prefix count equals full sequence count */
fn seq_count_prefix_full_eq(s: Seq<char>, target: char)
    ensures
        seq_count_prefix(s, s.len(), target) == seq_count(s, target),
{
    proof {
        if s.len() == 0 {
            assert(seq_count_prefix(s, 0, target) == 0);
            assert(seq_count(s, target) == 0);
        } else {
            // unfold definitions and apply induction on the tail
            assert(seq_count_prefix(s, s.len(), target) ==
                if s.len() == 0 { 0 } else {
                    let rest = seq_count_prefix(s.drop_first(), s.len() - 1, target);
                    if s[0] == target { rest + 1 } else { rest }
                }
            );
            assert(seq_count(s, target) ==
                if s.len() == 0 { 0 } else {
                    let rest2 = seq_count(s.drop_first(), target);
                    if s[0] == target { rest2 + 1 } else { rest2 }
                }
            );
            seq_count_prefix_full_eq(s.drop_first(), target);
            assert(seq_count_prefix(s.drop_first(), s.len() - 1, target) == seq_count(s.drop_first(), target));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, statuses: Vec<char>) -> (result: i8)
    requires valid_input(n as int, statuses@)
    ensures result as int == expected_result(statuses@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): count statuses using prefix-count helper to avoid unsupported slice */
    let n_usize: usize = n as usize;
    let mut i: usize = 0usize;
    let mut cnt_i: usize = 0usize;
    let mut cnt_a: usize = 0usize;

    while i < n_usize
        invariant
            0 <= i as int && i as int <= n as int,
            cnt_i as int == seq_count_prefix(statuses@, i as int, 'I'),
            cnt_a as int == seq_count_prefix(statuses@, i as int, 'A'),
        decreases
            (n as int) - (i as int)
    {
        let ch = statuses.get(i).unwrap();
        if *ch == 'I' {
            cnt_i = cnt_i + 1;
        } else if *ch == 'A' {
            cnt_a = cnt_a + 1;
        }
        i = i + 1;
    }

    proof {
        seq_count_prefix_full_eq(statuses@, 'I');
        seq_count_prefix_full_eq(statuses@, 'A');
        assert(cnt_i as int == seq_count(statuses@, 'I'));
        assert(cnt_a as int == seq_count(statuses@, 'A'));
    }

    let result: i8 = if cnt_i == 0 { cnt_a as i8 } else if cnt_i == 1 { 1 } else { 0 };

    proof {
        assert(cnt_i as int == count_status(statuses@, 'I'));
        assert(cnt_a as int == count_status(statuses@, 'A'));
        if cnt_i == 0 {
            assert(expected_result(statuses@) == cnt_a as int);
            assert(result as int == cnt_a as int);
        } else if cnt_i == 1 {
            assert(expected_result(statuses@) == 1);
            assert(result as int == 1);
        } else {
            assert(expected_result(statuses@) == 0);
            assert(result as int == 0);
        }
    }

    result
}
// </vc-code>


}

fn main() {}