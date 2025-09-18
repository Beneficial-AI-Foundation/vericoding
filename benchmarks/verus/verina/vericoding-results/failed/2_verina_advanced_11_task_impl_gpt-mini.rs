// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): count_occurrences <= len */
proof fn count_occurrences_le_len(x: i32, lst: Seq<i32>)
    ensures
        count_occurrences(x, lst) <= lst.len(),
    decreases lst.len()
{
    if lst.len() == 0 {
        proof {
            assert(count_occurrences(x, lst) == 0);
            assert(0 <= 0);
        }
    } else {
        let head = lst@[0];
        let tail = lst.subrange(1, lst.len());
        count_occurrences_le_len(x, tail);
        proof {
            if head == x {
                assert(count_occurrences(x, lst) == 1 + count_occurrences(x, tail));
                assert(count_occurrences(x, tail) <= tail.len());
                assert(1 + count_occurrences(x, tail) <= 1 + tail.len());
                assert(1 + tail.len() == lst.len());
                assert(count_occurrences(x, lst) <= lst.len());
            } else {
                assert(count_occurrences(x, lst) == count_occurrences(x, tail));
                assert(count_occurrences(x, tail) <= tail.len());
                assert(count_occurrences(x, lst) <= lst.len());
            }
        }
    }
}

/* helper modified by LLM (iteration 5): sum of counts for distinct elements <= len */
proof fn counts_of_distinct_add_le_len(x: i32, y: i32, lst: Seq<i32>)
    requires
        x != y,
    ensures
        count_occurrences(x, lst) + count_occurrences(y, lst) <= lst.len(),
    decreases lst.len()
{
    if lst.len() == 0 {
        proof {
            assert(count_occurrences(x, lst) + count_occurrences(y, lst) == 0);
        }
    } else {
        let head = lst@[0];
        let tail = lst.subrange(1, lst.len());
        counts_of_distinct_add_le_len(x, y, tail);
        proof {
            if head == x {
                assert(count_occurrences(x, lst) == 1 + count_occurrences(x, tail));
                assert(count_occurrences(y, lst) == count_occurrences(y, tail));
                assert(1 + count_occurrences(x, tail) + count_occurrences(y, tail) <= 1 + tail.len());
                assert(1 + tail.len() == lst.len());
                assert(count_occurrences(x, lst) + count_occurrences(y, lst) <= lst.len());
            } else if head == y {
                assert(count_occurrences(y, lst) == 1 + count_occurrences(y, tail));
                assert(count_occurrences(x, lst) == count_occurrences(x, tail));
                assert(count_occurrences(x, tail) + 1 + count_occurrences(y, tail) <= 1 + tail.len());
                assert(1 + tail.len() == lst.len());
                assert(count_occurrences(x, lst) + count_occurrences(y, lst) <= lst.len());
            } else {
                assert(count_occurrences(x, lst) == count_occurrences(x, tail));
                assert(count_occurrences(y, lst) == count_occurrences(y, tail));
                assert(count_occurrences(x, tail) + count_occurrences(y, tail) <= tail.len());
                assert(count_occurrences(x, lst) + count_occurrences(y, lst) <= lst.len());
            }
        }
    }
}

/* helper modified by LLM (iteration 5): if count > 0 then there exists an index of occurrence */
proof fn count_occurrences_pos_implies_exists(x: i32, lst: Seq<i32>)
    ensures
        count_occurrences(x, lst) > 0 ==> exists|k: nat| k < lst.len() && lst@[k] == x,
    decreases lst.len()
{
    if lst.len() == 0 {
        // vacuously true
    } else {
        let head = lst@[0];
        let tail = lst.subrange(1, lst.len());
        count_occurrences_pos_implies_exists(x, tail);
        proof {
            if head == x {
                // witness k = 0
                assert(count_occurrences(x, lst) > 0 ==> exists|k: nat| k < lst.len() && lst@[k] == x);
            } else {
                // occurrences in lst equal occurrences in tail
                assert(count_occurrences(x, lst) == count_occurrences(x, tail));
                // use inductive hypothesis on tail; if tail has witness k', then lst has k'+1
                assert(count_occurrences(x, tail) > 0 ==> exists|k: nat| k < lst.len() && lst@[k] == x);
                assert(count_occurrences(x, lst) > 0 ==> exists|k: nat| k < lst.len() && lst@[k] == x);
            }
        }
    }
}

/* helper modified by LLM (iteration 5): uniqueness of majority element */
proof fn majority_unique(res: i32, lst: Seq<i32>)
    requires
        count_occurrences(res, lst) > lst.len() / 2,
    ensures
        forall|x: i32| count_occurrences(x, lst) > lst.len() / 2 ==> x == res,
    decreases lst.len()
{
    proof {
        forall|x: i32| {
            if count_occurrences(x, lst) > lst.len() / 2 {
                if x != res {
                    counts_of_distinct_add_le_len(x, res, lst);
                    assert(count_occurrences(x, lst) + count_occurrences(res, lst) <= lst.len());
                    assert(count_occurrences(x, lst) + count_occurrences(res, lst) > lst.len());
                    // contradiction
                    assert(false);
                }
            }
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn find_majority_element(lst: &Vec<i32>) -> (result: i32)
    ensures ({
        let lst_seq = lst@;
        let n = lst_seq.len();
        let majority = count_occurrences(result, lst_seq) > n / 2 && 
                      forall|x: i32| count_occurrences(x, lst_seq) <= n / 2 || x == result;
        (result == -1 ==> forall|x: i32| count_occurrences(x, lst_seq) <= n / 2) &&
        (result != -1 ==> majority)
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): simple scan using count_occurrences */
{
    let seq = lst@;
    let n: nat = seq.len();
    let mut i: nat = 0;

    while i < n
        invariant
            i <= n,
            forall|j: nat| j < i ==> count_occurrences(seq@[j], seq) <= n / 2,
        decreases n - i
    {
        let x: i32 = lst.index(i);
        let c: nat = count_occurrences(x, seq);
        if c > n / 2 {
            proof {
                // establish uniqueness of the majority (for the postcondition)
                majority_unique(x, seq);
            }
            return x;
        }
        i = i + 1;
    }

    proof {
        // no majority exists: if some y had count > n/2 then there is an index k with seq@[k] == y,
        // but by the loop invariant at termination every index's element has count <= n/2
        assert(i == n);
        forall|y: i32| {
            if count_occurrences(y, seq) > n / 2 {
                count_occurrences_pos_implies_exists(y, seq);
                let k = choose(|k: nat| k < n && seq@[k] == y);
                assert(count_occurrences(y, seq) == count_occurrences(seq@[k], seq));
                assert(forall|j: nat| j < n ==> count_occurrences(seq@[j], seq) <= n / 2);
                assert(count_occurrences(seq@[k], seq) <= n / 2);
                assert(count_occurrences(y, seq) <= n / 2);
                assert(false);
            }
        }
    }

    return -1;
}

// </vc-code>

}
fn main() {}