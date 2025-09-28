// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_pair_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int| 0 <= i < j < l.len() && l[i] + l[j] == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix helper functions to use proper indexing and ghost parameters */

spec fn has_pair_sum_to_zero_helper(l: Seq<int>, start: nat) -> bool {
    exists|j: nat| start < j < l.len() && l[start] + l[j] == 0
}

proof fn pair_exists_if_found(l: Seq<int>, i: nat, j: nat)
    requires
        0 <= i < j < l.len(),
        l[i] + l[j] == 0
    ensures
        has_pair_sum_to_zero(l)
{
}

proof fn no_pair_if_complete(l: Seq<int>)
    requires
        forall|i: nat, j: nat| 0 <= i < j < l.len() ==> l[i] + l[j] != 0
    ensures
        !has_pair_sum_to_zero(l)
{
}
// </vc-helpers>

// <vc-spec>
fn pairs_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_pair_sum_to_zero(l@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix sequence mapping syntax and ghost block placement */
{
    let len = l.len();
    let s = l@.map(|x: i8| x as int);
    proof {
        let mut i: nat = 0;
        while i < len
            invariant
                0 <= i <= len,
                forall|ii: nat, jj: nat| 0 <= ii < i && ii < jj < len ==> s[ii] + s[jj] != 0
            decreases len - i
        {
            let mut j: nat = i + 1;
            while j < len
                invariant
                    i < j <= len,
                    forall|jj: nat| i < jj < j ==> s[i] + s[jj] != 0
                decreases len - j
            {
                if s[i] + s[j] == 0 {
                    pair_exists_if_found(s, i, j);
                    return true;
                }
                j += 1;
            }
            i += 1;
        }
        no_pair_if_complete(s);
    }
    false
}
// </vc-code>


}

fn main() {}