// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(diameters: Seq<int>) -> bool {
    diameters.len() > 0 && forall|i: int| 0 <= i < diameters.len() ==> diameters[i] > 0
}

spec fn num_distinct(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.subrange(1, s.len() as int).contains(s[0]) {
        num_distinct(s.subrange(1, s.len() as int))
    } else {
        1 + num_distinct(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
fn seq_contains(s: Seq<int>, x: int) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        false
    } else if s[0] == x {
        true
    } else {
        seq_contains(s.subrange(1, s.len() as int), x)
    }
}

proof fn lemma_seq_contains_equals_spec(s: Seq<int>, x: int)
    ensures
        seq_contains(s, x) <==> s.contains(x)
{
    if s.len() == 0 {
        assert(seq_contains(s, x) == false && s.contains(x) == false);
    } else {
        lemma_seq_contains_equals_spec(s.subrange(1, s.len() as int), x);
        assert(seq_contains(s, x) == (s[0] == x || seq_contains(s.subrange(1, s.len() as int), x)));
        assert(s.contains(x) == (s[0] == x || s.subrange(1, s.len() as int).contains(x)));
    }
}

fn exec_num_distinct(s: Seq<int>) -> (count: int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        let tail = s.subrange(1, s.len() as int);
        let count_tail = exec_num_distinct(tail);
        if seq_contains(tail, s[0]) {
            count_tail
        } else {
            count_tail + 1
        }
    }
}

proof fn lemma_exec_num_distinct_equals_spec(s: Seq<int>)
    ensures
        exec_num_distinct(s) == num_distinct(s)
{
    if s.len() == 0 {
        assert(exec_num_distinct(s) == 0 && num_distinct(s) == 0);
    } else {
        let tail = s.subrange(1, s.len() as int);
        lemma_exec_num_distinct_equals_spec(tail);
        lemma_seq_contains_equals_spec(tail, s[0]);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(diameters: Vec<i8>) -> (result: i8)
    requires 
        valid_input(diameters@.map(|i, x| x as int)),
    ensures 
        result as int == num_distinct(diameters@.map(|i, x| x as int)),
        result as int >= 1,
        result as int <= diameters@.len(),
// </vc-spec>
// <vc-code>
{
    let s = diameters@.map(|i, x| x as int);
    let count_int = exec_num_distinct(s);
    lemma_exec_num_distinct_equals_spec(s);
    assert(count_int <= i8::MAX as int);
    let result = count_int as i8;
    result
}
// </vc-code>


}

fn main() {}