// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n
}

spec fn count_local_extrema(n: int, a: Seq<int>) -> int
    recommends valid_input(n, a)
{
    Set::<int>::new(|i: int| 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))).len() as int
}

spec fn is_local_extremum(a: Seq<int>, i: int) -> bool
    recommends 0 <= i < a.len()
{
    1 <= i < a.len() - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate Vec entries to mapped Seq and equivalence of local extremum */
proof fn vec_local_extremum_equiv(a: &Vec<i8>, i: int)
    requires
        0 <= i < a@.len(),
    ensures
        is_local_extremum(a@.map_values(|x: i8| x as int), i) == (
            1 <= i < a@.len() - 1 &&
            ((( (a@)@[i] as int) > ((a@)@[i-1] as int) && ((a@)@[i] as int) > ((a@)@[i+1] as int)) ||
             (((a@)@[i] as int) < ((a@)@[i-1] as int) && ((a@)@[i] as int) < ((a@)@[i+1] as int)))
        ),
{
    proof {
        if 1 <= i < a@.len() - 1 {
            assert (a@.map_values(|x: i8| x as int))@[i] == ((a@)@[i] as int);
            assert (a@.map_values(|x: i8| x as int))@[i-1] == ((a@)@[i-1] as int);
            assert (a@.map_values(|x: i8| x as int))@[i+1] == ((a@)@[i+1] as int);
            assert is_local_extremum(a@.map_values(|x: i8| x as int), i) == (
                1 <= i < a@.len() - 1 &&
                (((a@.map_values(|x: i8| x as int))@[i] > (a@.map_values(|x: i8| x as int))@[i-1] && (a@.map_values(|x: i8| x as int))@[i] > (a@.map_values(|x: i8| x as int))@[i+1]) ||
                 ((a@.map_values(|x: i8| x as int))@[i] < (a@.map_values(|x: i8| x as int))@[i-1] && (a@.map_values(|x: i8| x as int))@[i] < (a@.map_values(|x: i8| x as int))@[i+1]))
            );
            assert ((a@.map_values(|x: i8| x as int))@[i] > (a@.map_values(|x: i8| x as int))@[i-1]) == (((a@)@[i] as int) > ((a@)@[i-1] as int));
            assert ((a@.map_values(|x: i8| x as int))@[i] > (a@.map_values(|x: i8| x as int))@[i+1]) == (((a@)@[i] as int) > ((a@)@[i+1] as int));
            assert ((a@.map_values(|x: i8| x as int))@[i] < (a@.map_values(|x: i8| x as int))@[i-1]) == (((a@)@[i] as int) < ((a@)@[i-1] as int));
            assert ((a@.map_values(|x: i8| x as int))@[i] < (a@.map_values(|x: i8| x as int))@[i+1]) == (((a@)@[i] as int) < ((a@)@[i+1] as int));
            assert is_local_extremum(a@.map_values(|x: i8| x as int), i) == (
                1 <= i < a@.len() - 1 &&
                ((( (a@)@[i] as int) > ((a@)@[i-1] as int) && ((a@)@[i] as int) > ((a@)@[i+1] as int)) ||
                 (((a@)@[i] as int) < ((a@)@[i-1] as int) && ((a@)@[i] as int) < ((a@)@[i+1] as int)))
            );
        } else {
            assert !(1 <= i < a@.len() - 1);
            assert is_local_extremum(a@.map_values(|x: i8| x as int), i) == false;
            assert (1 <= i < a@.len() - 1 && (((a@.map_values(|x: i8| x as int))@[i] > (a@.map_values(|x: i8| x as int))@[i-1] && (a@.map_values(|x: i8| x as int))@[i] > (a@.map_values(|x: i8| x as int))@[i+1]) || ((a@.map_values(|x: i8| x as int))@[i] < (a@.map_values(|x: i8| x as int))@[i-1] && (a@.map_values(|x: i8| x as int))@[i] < (a@.map_values(|x: i8| x as int))@[i+1]))) == false;
            assert is_local_extremum(a@.map_values(|x: i8| x as int), i) == (1 <= i < a@.len() - 1 && (((a@)@[i] as int) > ((a@)@[i-1] as int) && ((a@)@[i] as int) > ((a@)@[i+1] as int) || ((a@)@[i] as int) < ((a@)@[i-1] as int) && ((a@)@[i] as int) < ((a@)@[i+1] as int)));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures 
        result >= 0,
        n <= 2 ==> result == 0,
        n > 2 ==> result <= n - 2,
        result as int == count_local_extrema(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): count local extrema in vector */
{
    let mut idx: int = 1;
    let mut cnt: int = 0;
    while idx < (n as int - 1)
        invariant
            1 <= idx <= n as int,
            cnt == Set::<int>::new(|j: int| 1 <= j < idx && is_local_extremum(a@.map_values(|x: i8| x as int), j)).len() as int,
        decreases n as int - idx
    {
        let ai = ((a@)@[idx] as int);
        let prev = ((a@)@[idx - 1] as int);
        let next = ((a@)@[idx + 1] as int);
        let cond = (ai > prev && ai > next) || (ai < prev && ai < next);
        if cond {
            cnt = cnt + 1;
        }
        proof {
            assert 0 <= idx < a@.len();
            vec_local_extremum_equiv(&a, idx);
            if cond {
                assert is_local_extremum(a@.map_values(|x: i8| x as int), idx);
            } else {
                assert !is_local_extremum(a@.map_values(|x: i8| x as int), idx);
            }
            assert cnt == Set::<int>::new(|j: int| 1 <= j < idx + 1 && is_local_extremum(a@.map_values(|x: i8| x as int), j)).len() as int;
        }
        idx = idx + 1;
    }
    proof {
        assert cnt == Set::<int>::new(|j: int| 1 <= j < n as int - 1 && is_local_extremum(a@.map_values(|x: i8| x as int), j)).len() as int;
    }
    let result = cnt as i8;
    result
}

// </vc-code>


}

fn main() {}