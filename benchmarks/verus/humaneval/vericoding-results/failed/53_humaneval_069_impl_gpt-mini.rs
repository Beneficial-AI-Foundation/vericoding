// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

spec fn count(s: Seq<int>, x: int) -> int {
    s.filter(|i: int| i == x).len() as int
}

spec fn max_seq(s: Seq<int>) -> int
    recommends s.len() > 0
{
    if s.len() == 1 { s[0] } else { choose|x: int| s.contains(x) }
}

spec fn valid_input(lst: Seq<int>) -> bool {
    lst.len() > 0 && forall|i: int| 0 <= i < lst.len() ==> lst[i] > 0
}

spec fn valid_result(lst: Seq<int>, result: int) -> bool
    recommends valid_input(lst)
{
    if result == -1 {
        forall|x: int| #![auto] lst.contains(x) ==> count(lst, x) < x
    } else {
        result > 0 &&
        lst.contains(result) && 
        count(lst, result) >= result &&
        forall|y: int| #![auto] lst.contains(y) && count(lst, y) >= y ==> y <= result
    }
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove count non-negativity */
proof fn lemma_count_nonneg(s: Seq<int>, x: int)
    ensures
        count(s, x) >= 0,
{
    assert(count(s, x) >= 0);
}

/* helper modified by LLM (iteration 5): relate Seq.contains to existence of an index */
proof fn lemma_contains_index(s: Seq<int>, x: int)
    ensures
        s.contains(x) ==> exists|j: int| 0 <= j && j < s.len() && s[j] == x,
{
    assert(s.contains(x) ==> exists|j: int| 0 <= j && j < s.len() && s[j] == x);
}

// </vc-helpers>

// <vc-spec>
fn search(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|_index: int, x: i8| x as int))
    ensures valid_result(lst@.map(|_index: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate sequence, track max candidate meeting count>=value and prove result */
    let s: Seq<int> = lst@.map(|_index: int, x: i8| x as int);
    let n: int = s.len() as int;
    let mut i: int = 0;
    let mut candidate_index: int = -1;
    let mut candidate_value: int = -1;

    while i < n
        invariant
            0 <= i && i <= n,
            (candidate_index == -1) ==> candidate_value == -1,
            (candidate_index != -1) ==> (0 <= candidate_index && candidate_index < i && candidate_value == s@[candidate_index]),
            forall|j: int| 0 <= j && j < i ==> (count(s, s@[j]) >= s@[j] ==> s@[j] <= candidate_value),
        decreases n - i
    {
        let val: int = s@[i];
        if count(s, val) >= val {
            if candidate_index == -1 || val > candidate_value {
                candidate_index = i;
                candidate_value = val;
            }
        }
        i = i + 1;
    }

    if candidate_index == -1 {
        proof {
            assert(i == n);
            // From invariant at loop exit: for all j < i we have count(s, s@[j]) < s@[j]
            assert((candidate_index == -1) ==> (forall|j: int| 0 <= j && j < i ==> count(s, s@[j]) < s@[j]));
            assert(forall|j: int| 0 <= j && j < i ==> count(s, s@[j]) < s@[j]);
            // Hence for every value contained in s the count is less than the value
            assert(forall|x: int| s.contains(x) ==> count(s, x) < x);
        }
        -1
    } else {
        let k: usize = candidate_index as nat;
        proof {
            assert(candidate_index != -1);
            assert(0 <= candidate_index && candidate_index < n);
            assert(candidate_value == s@[candidate_index]);
            assert(count(s, candidate_value) >= candidate_value);
            assert(forall|j: int| 0 <= j && j < n ==> (count(s, s@[j]) >= s@[j] ==> s@[j] <= candidate_value));
            assert(forall|y: int| s.contains(y) && count(s,y) >= y ==> y <= candidate_value);
        }
        lst[k]
    }
}

// </vc-code>


}

fn main() {}