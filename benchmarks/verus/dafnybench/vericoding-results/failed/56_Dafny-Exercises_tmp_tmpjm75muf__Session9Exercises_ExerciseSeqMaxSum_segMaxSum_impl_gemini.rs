// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(v: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j when 0 <= i <= j <= v.len()
{
    if i == j {
        0 as int
    } else {
        sum(v, i, (j-1) as int) + v[(j-1) as int]
    }
}

spec fn sum_max_to_right(v: Seq<int>, i: int, s: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 ==> sum(v, l, ss) <= s
}

spec fn sum2(v: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j - i when 0 <= i <= j <= v.len()
{
    if i == j {
        0 as int
    } else {
        v[i as int] + sum2(v, (i+1) as int, j)
    }
}

spec fn sum_max_to_right2(v: Seq<int>, j: int, i: int, s: int) -> bool
    recommends 0 <= j <= i < v.len()
{
    forall|l: int, ss: int| j <= l <= i && ss == i + 1 ==> sum2(v, l, ss) <= s
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Proves that extending a sum by one element works as expected. */
proof fn lemma_sum_extend(v: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j < v.len(),
    ensures
        sum(v, i, j + 1) == sum(v, i, j) + v[j as int],
{
}
// </vc-helpers>

// <vc-spec>
fn seg_max_sum(v: &[i32], i: usize) -> (result: (i32, usize))
    requires v.len() > 0 && i < v.len()
    ensures 
        result.1 <= i,
        result.0 == sum(v@.map_values(|x: i32| x as int), result.1 as int, (i+1) as int),
        sum_max_to_right(v@.map_values(|x: i32| x as int), i as int, result.0 as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error and corrected proof blocks logic. */
{
    if i == 0 {
        return (v[0], 0);
    }

    let (prev_s, prev_j) = seg_max_sum(v, (i - 1) as usize);

    let ghost v_int = v@.map_values(|x: i32| x as int);
    
    if prev_s > 0 {
        let current_s = prev_s + v[i];
        let current_j = prev_j;

        proof {
            let s_curr = current_s as int;
            let i_int = i as int;
            let j_int = current_j as int;

            lemma_sum_extend(v_int, j_int, i_int);

            assert forall|l: int| 0 <= l <= i_int implies sum(v_int, l, i_int + 1) <= s_curr by {
                lemma_sum_extend(v_int, l, i_int);
                if l < i_int {
                    assert(sum_max_to_right(v_int, i_int - 1, prev_s as int));
                } else { // l == i_int
                    assert(0 <= prev_s as int);
                }
            }
            assert(sum_max_to_right(v_int, i_int, s_curr));
        }

        (current_s, current_j)
    } else {
        let current_s = v[i];
        let current_j = i;

        proof {
            let s_curr = current_s as int;
            let i_int = i as int;
            
            assert(s_curr == sum(v_int, i_int, i_int + 1));

            assert forall|l: int| 0 <= l <= i_int implies sum(v_int, l, i_int + 1) <= s_curr by {
                lemma_sum_extend(v_int, l, i_int);
                if l < i_int {
                    assert(sum_max_to_right(v_int, i_int - 1, prev_s as int));
                    assert(prev_s as int <= 0);
                } else { // l == i_int
                    assert(sum(v_int, i_int, i_int) == 0);
                }
            }
            assert(sum_max_to_right(v_int, i_int, s_curr));
        }

        (current_s, current_j)
    }
}
// </vc-code>

}
fn main() {}