// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_triple_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int, k: int| 0 <= i < j < k < l.len() && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn triples_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_triple_sum_to_zero(l@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    let n = l.len();
    let s = l@.map(|i, x: i8| x as int);
    let n_int = n as int;

    if n < 3 {
        assert forall|i: int, j: int, k: int| 0 <= i < j < k < n_int implies false by {
            if 0 <= i < j < k < n_int {
                assert(k >= j + 1);
                assert(j >= i + 1);
                assert(k >= i + 2);
                assert(n_int > k);
                assert(n_int >= k + 1);
                assert(n_int >= i + 3);
                assert(n_int >= 3);
            }
        };
        assert(!has_triple_sum_to_zero(s));
        return false;
    }

    let mut i: usize = 0;
    while i < n - 2
        invariant
            0 <= i <= n - 2,
            forall|i_p: int, j_p: int, k_p: int|
                0 <= i_p < (i as int) && i_p < j_p < k_p < n_int ==>
                s[i_p] + s[j_p] + s[k_p] != 0,
    {
        let mut j: usize = i + 1;
        while j < n - 1
            invariant
                (i as int) + 1 <= (j as int) && (j as int) <= n_int - 1,
                forall|i_p: int, j_p: int, k_p: int|
                    (0 <= i_p < (i as int) || (i_p == (i as int) && (i as int) < j_p < (j as int))) &&
                    i_p < j_p < k_p < n_int ==>
                    s[i_p] + s[j_p] + s[k_p] != 0,
        {
            let mut k: usize = j + 1;
            while k < n
                invariant
                    (j as int) + 1 <= (k as int) && (k as int) <= n_int,
                    forall|i_p: int, j_p: int, k_p: int|
                        (
                            0 <= i_p < (i as int) ||
                            (i_p == (i as int) && (i as int) < j_p < (j as int)) ||
                            (i_p == (i as int) && j_p == (j as int) && (j as int) < k_p < (k as int))
                        ) &&
                        i_p < j_p < k_p < n_int ==>
                        s[i_p] + s[j_p] + s[k_p] != 0,
            {
                if l[i] as int + l[j] as int + l[k] as int == 0 {
                    assert(s[i as int] + s[j as int] + s[k as int] == 0);
                    assert(has_triple_sum_to_zero(s));
                    return true;
                }
                k = k + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    assert(!has_triple_sum_to_zero(s)) by {
        let final_i = (n - 2) as int;
        assert forall|i_p: int, j_p: int, k_p: int|
            0 <= i_p < j_p < k_p < n_int implies s[i_p] + s[j_p] + s[k_p] != 0
        by {
            if i_p >= final_i {
                assert(j_p > i_p >= n_int - 2);
                assert(j_p >= n_int - 1);
                assert(k_p > j_p >= n_int - 1);
                assert(k_p >= n_int);
                assert(k_p < n_int);
                assert(false);
            }
        };
    };

    return false;
}
// </vc-code>


}

fn main() {}