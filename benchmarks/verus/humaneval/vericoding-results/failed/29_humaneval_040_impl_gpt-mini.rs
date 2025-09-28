// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_triple_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int, k: int| 0 <= i < j < k < l.len() && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): produce existence witness using Vec indices */
proof fn make_exists_triple(l: Vec<i8>, i: int, j: int, k: int)
    requires
        0 <= i < j < k < (l.len() as int),
        (l[i as usize] as int) + (l[j as usize] as int) + (l[k as usize] as int) == 0,
    ensures
        has_triple_sum_to_zero(l@.map(|_, x: i8| x as int)),
{
    proof {
        assert(0 <= i && i < j && j < k && k < (l.len() as int));
        assert((l[i as usize] as int) + (l[j as usize] as int) + (l[k as usize] as int) == 0);
        assert(exists|ii: int, jj: int, kk: int|
            0 <= ii < jj < kk < (l.len() as int) &&
            (l[ii as usize] as int) + (l[jj as usize] as int) + (l[kk as usize] as int) == 0
        );
    }
}

// </vc-helpers>

// <vc-spec>
fn triples_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_triple_sum_to_zero(l@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implement triple-search loops and use helper to prove existence when found */
{
    let n = l.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int && i as int <= (l.len() as int),
            forall|ii: int, jj: int, kk: int|
                0 <= ii < jj < kk < (l.len() as int) ==> (l[ii as usize] as int) + (l[jj as usize] as int) + (l[kk as usize] as int) != 0,
        decreases (n - i)
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                0 <= i as int && i as int <= (l.len() as int),
                i as int + 1 <= j as int && j as int <= (l.len() as int),
                forall|ii: int, jj: int, kk: int|
                    0 <= ii < jj < kk < (l.len() as int) && (ii < i as int || (ii == i as int && jj < j as int)) ==> (l[ii as usize] as int) + (l[jj as usize] as int) + (l[kk as usize] as int) != 0,
            decreases (n - j)
        {
            let mut k: usize = j + 1;
            while k < n
                invariant
                    0 <= i as int && i as int <= (l.len() as int),
                    i as int + 1 <= j as int && j as int <= (l.len() as int),
                    j as int + 1 <= k as int && k as int <= (l.len() as int),
                    forall|ii: int, jj: int, kk: int|
                        0 <= ii < jj < kk < (l.len() as int) && (ii < i as int || (ii == i as int && jj < j as int) || (ii == i as int && jj == j as int && kk < k as int)) ==> (l[ii as usize] as int) + (l[jj as usize] as int) + (l[kk as usize] as int) != 0,
                decreases (n - k)
            {
                let sum = (l[i] as i32) + (l[j] as i32) + (l[k] as i32);
                if sum == 0 {
                    proof {
                        let ii: int = i as int;
                        let jj: int = j as int;
                        let kk: int = k as int;
                        assert((l[ii as usize] as int) + (l[jj as usize] as int) + (l[kk as usize] as int) == 0);
                        make_exists_triple(l, ii, jj, kk);
                    }
                    return true;
                }
                k = k + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}

// </vc-code>


}

fn main() {}