// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(x: i32, lst: Seq<i32>) -> nat {
    lst.filter(|y: i32| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): uniqueness property from majority count (kept as in previous iteration) */
proof fn lemma_uniqueness_from_count(s: Seq<i32>, m: i32)
    requires
        count_occurrences(m, s) > s.len() / 2,
    ensures
        forall|x: i32| count_occurrences(x, s) <= s.len() / 2 || x == m,
{
    let n = s.len();
    let cm = count_occurrences(m, s);
    assert(cm > n / 2);

    // Any occurrence of x distinct from m must be among elements != m
    assert(forall|x: i32|
        x == m || count_occurrences(x, s) <= s.filter(|y: i32| y != m).len()
    );

    // The elements equal to m and those not equal to m partition the sequence
    assert(s.filter(|y: i32| y == m).len() + s.filter(|y: i32| y != m).len() == n);

    // Thus the number of elements != m equals n - cm
    assert(s.filter(|y: i32| y != m).len() == n - cm);

    assert(forall|x: i32| x == m || count_occurrences(x, s) <= n - cm);

    assert(n - cm < n / 2) by {
        // Since cm > n/2, then n - cm < n/2 over natural numbers
    };

    assert(forall|x: i32| x == m || count_occurrences(x, s) <= n / 2);
}

/* helper modified by LLM (iteration 2): fix nat/int index in universal quantification */
proof fn lemma_count_zero_if_no_equal(s: Seq<i32>, x: i32)
    requires
        forall|j: nat| j < s.len() ==> s[j as int] != x,
    ensures
        count_occurrences(x, s) == 0,
{
    // If no element equals x, the filtered sequence is empty
    assert(s.filter(|y: i32| y == x).len() == 0);
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
{
    /* code modified by LLM (iteration 2): fix nat/int index mismatches in quantified expressions */
    let lst_seq = lst@;
    let n: usize = lst.len();

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            lst@ == lst_seq,
            forall|x: i32| (exists|j: nat| j < i && lst_seq[j as int] == x) ==> count_occurrences(x, lst_seq) <= (lst_seq.len() / 2),
        decreases n - i
    {
        let v = lst[i];
        let mut k: usize = 0;
        let mut occ: usize = 0;
        while k < n
            invariant
                k <= n,
                lst@ == lst_seq,
                occ as nat == count_occurrences(v, lst_seq.subrange(0, k as int)),
            decreases n - k
        {
            if lst[k] == v {
                occ = occ + 1;
            }
            k = k + 1;
        }
        proof {
            assert(occ as nat == count_occurrences(v, lst_seq));
        }
        if occ > n / 2 {
            let res = v;
            proof {
                assert(count_occurrences(res, lst_seq) > lst_seq.len() / 2);
                lemma_uniqueness_from_count(lst_seq, res);
            }
            return res;
        }
        proof {
            assert(count_occurrences(v, lst_seq) <= lst_seq.len() / 2);
        }
        i = i + 1;
    }

    proof {
        // Show: for all x, count(x) <= n/2
        assert(forall|x: i32| if (exists|j: nat| j < lst_seq.len() && lst_seq[j as int] == x) {
            // x appears in the list; pick a witness j < n, then apply the loop invariant at i == n
            count_occurrences(x, lst_seq) <= lst_seq.len() / 2
        } else {
            // x does not appear in the list, so its count is zero
            lemma_count_zero_if_no_equal(lst_seq, x);
            count_occurrences(x, lst_seq) == 0
        });
    }

    -1
}
// </vc-code>

}
fn main() {}