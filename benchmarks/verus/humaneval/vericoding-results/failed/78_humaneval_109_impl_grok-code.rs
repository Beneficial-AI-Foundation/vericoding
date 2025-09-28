// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn rotate_right(arr: Seq<int>, k: int) -> Seq<int>
    recommends 0 <= k <= arr.len()
{
    if arr.len() == 0 {
        arr
    } else if k == 0 {
        arr
    } else {
        arr.subrange((arr.len() - k) as int, arr.len() as int) + arr.subrange(0, (arr.len() - k) as int)
    }
}

// </vc-preamble>

// <vc-helpers>
exec fn rotate_right_vec(v: &Vec<i8>, k: usize) -> Vec<i8>
    requires
        0 <= k <= v.len()
    {
        if v.len() == 0 {
            Vec::new()
        } else if k == 0 {
            v.clone()
        } else {
            let len = v.len();
            let mut res = Vec::new();
            let m = len - k;
            for i in m..len {
                res.push(v[i]);
            }
            for i in 0..m {
                res.push(v[i]);
            }
            res
        }
    }

/* helper modified by LLM (iteration 5): Fixed compilation by removing duplicate function definition and adjusted comment */
exec fn is_sorted_vec(v: &Vec<i8>) -> bool
    requires
        true
    {
        let len = v.len();
        if len <= 1 {
            return true;
        }
        let mut i: usize = 0;
        while i < len - 1
            invariant
                0 <= i <= len - 1,
                forall |j: int| 0 <= j < i ==> #[trigger] (v@[j] as int <= v@[j + 1] as int)
            decreases len - i
        {
            if v[i] > v[i + 1] {
                return false;
            }
            i += 1;
        }
        true
    }
// </vc-helpers>

// <vc-spec>
fn move_one_ball(arr: Vec<i8>) -> (result: bool)
    requires 
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i as int] != arr[j as int]
    ensures 
        arr.len() == 0 ==> result == true,
        result == true ==> (arr.len() == 0 || exists|k: int| #[trigger] is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), k)) && 0 <= k < arr.len()),
        result == false ==> forall|k: int| 0 <= k < arr.len() ==> !is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), k))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Verified compilation fix by removing duplicate fn in helpers */
    if arr.len() == 0 {
        return true;
    }
    let len = arr.len();
    for k in 0..len {
        let rotated = rotate_right_vec(&arr, k);
        if is_sorted_vec(&rotated) {
            return true;
        }
    }
    false
}
// </vc-code>


}

fn main() {}