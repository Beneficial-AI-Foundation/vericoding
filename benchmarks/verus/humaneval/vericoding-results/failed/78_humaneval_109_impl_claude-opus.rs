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
proof fn lemma_rotate_right_zero(arr: Seq<int>)
    ensures
        rotate_right(arr, 0) == arr
{
}

/* helper modified by LLM (iteration 5): Added trigger annotation to fix quantifier inference */
proof fn lemma_rotate_right_len(arr: Seq<int>)
    ensures
        arr.len() > 0 ==> rotate_right(arr, arr.len() as int) == arr
{
    if arr.len() > 0 {
        assert(arr.subrange(0, 0) =~= Seq::<int>::empty());
        assert(arr.subrange(0, arr.len() as int) =~= arr);
    }
}

fn check_rotation(arr: &Vec<i8>, k: usize) -> (result: bool)
    requires
        0 <= k < arr.len()
    ensures
        result == is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), k as int))
{
    let n = arr.len();
    if n == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            forall|j: int| 0 <= j < i ==> #[trigger] (rotate_right(arr@.map(|ii, x: i8| x as int), k as int)[j]) <= rotate_right(arr@.map(|ii, x: i8| x as int), k as int)[j + 1],
        decreases n - 1 - i
    {
        let curr_idx = ((k + i) % n) as usize;
        let next_idx = ((k + i + 1) % n) as usize;
        
        if arr[curr_idx] > arr[next_idx] {
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert forall|j: int| 0 <= j < n - 1 implies
            #[trigger] (rotate_right(arr@.map(|ii, x: i8| x as int), k as int)[j]) <= rotate_right(arr@.map(|ii, x: i8| x as int), k as int)[j + 1] by {
            assert(0 <= j < i);
        }
        assert(is_sorted(rotate_right(arr@.map(|ii, x: i8| x as int), k as int)));
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
    /* code modified by LLM (iteration 5): No change needed in main code body */
    let n = arr.len();
    
    if n == 0 {
        return true;
    }
    
    if n == 1 {
        proof {
            lemma_rotate_right_zero(arr@.map(|i, x: i8| x as int));
            assert(is_sorted(arr@.map(|i, x: i8| x as int)));
        }
        return true;
    }
    
    let mut k: usize = 0;
    let mut found = false;
    
    while k < n
        invariant
            0 <= k <= n,
            found ==> exists|j: int| 0 <= j < k && is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), j)),
            !found ==> forall|j: int| 0 <= j < k ==> !is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), j)),
        decreases n - k
    {
        if check_rotation(&arr, k) {
            found = true;
            break;
        }
        k = k + 1;
    }
    
    if found {
        proof {
            assert(exists|j: int| #[trigger] is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), j)) && 0 <= j < arr.len());
        }
    } else {
        proof {
            assert(k == n);
            assert forall|j: int| 0 <= j < n implies !is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), j)) by {
                assert(0 <= j < k);
            }
        }
    }
    
    found
}
// </vc-code>


}

fn main() {}