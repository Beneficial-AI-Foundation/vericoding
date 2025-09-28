// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(arr: Seq<int>) -> bool {
    forall|i: int| 0 <= i < arr.len() ==> arr[i] >= 0
}

spec fn is_ascending_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn is_descending_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] >= s[j]
}

spec fn should_sort_ascending(arr: Seq<int>) -> bool {
    arr.len() > 1 && (arr[0] + arr[arr.len() - 1]) % 2 == 1
}

spec fn should_sort_descending(arr: Seq<int>) -> bool {
    arr.len() > 1 && (arr[0] + arr[arr.len() - 1]) % 2 == 0
}

spec fn correctly_sorted(arr: Seq<int>, result: Seq<int>) -> bool {
    (arr.len() <= 1 ==> result == arr) &&
    (should_sort_ascending(arr) ==> is_ascending_sorted(result)) &&
    (should_sort_descending(arr) ==> is_descending_sorted(result))
}

fn sort_ascending(arr: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == arr.to_multiset(),
        is_ascending_sorted(result)
{
    assume(false);
    unreached()
}


fn sort_descending(arr: Seq<int>) -> (result: Seq<int>)
    ensures
        result.to_multiset() == arr.to_multiset(),
        is_descending_sorted(result)
{
    assume(false);
    unreached()
}

// </vc-preamble>

// <vc-helpers> 
/* helper modified by LLM (iteration 5): conversion from Seq<i8> to Seq<int> */
spec fn seq_i8_to_int(s: Seq<i8>) -> Seq<int> {
    s.map(|i: int, x: i8| x as int)
}

/* helper modified by LLM (iteration 5): check parity of first+last elements */
spec fn seq_first_last_parity_is_odd(s: Seq<i8>) -> bool {
    s.len() > 1 && (seq_i8_to_int(s)[0] + seq_i8_to_int(s)[s.len() - 1]) % 2 == 1
}
// </vc-helpers>


// <vc-spec>
fn sort_array(arr: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(arr@.map(|i: int, x: i8| x as int))
    ensures 
        result@.map(|i: int, x: i8| x as int).to_multiset() == arr@.map(|i: int, x: i8| x as int).to_multiset(),
        correctly_sorted(arr@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): selection sort using manual swap to avoid &mut borrow issue */
{
    let mut v = arr.clone();
    let n = v.len();
    if n > 1 {
        let is_asc = ((v[0] as i32 + v[n - 1] as i32) % 2) != 0;
        let mut i: usize = 0;
        while i < n
            invariant
                v.len() == n,
                seq_i8_to_int(v@).to_multiset() == arr@.map(|i: int, x: i8| x as int).to_multiset(),
                is_asc ==> (forall|a: int, b: int| 0 <= a < b < i as int ==> seq_i8_to_int(v@)[a] <= seq_i8_to_int(v@)[b]),
                !is_asc ==> (forall|a: int, b: int| 0 <= a < b < i as int ==> seq_i8_to_int(v@)[a] >= seq_i8_to_int(v@)[b]),
                is_asc ==> (forall|a: int, b: int| 0 <= a < i as int <= b < n as int ==> seq_i8_to_int(v@)[a] <= seq_i8_to_int(v@)[b]),
                !is_asc ==> (forall|a: int, b: int| 0 <= a < i as int <= b < n as int ==> seq_i8_to_int(v@)[a] >= seq_i8_to_int(v@)[b]),
            decreases n - i
        {
            let mut sel: usize = i;
            let mut j: usize = i + 1;
            while j < n
                invariant
                    v.len() == n,
                    sel < n,
                    i <= sel,
                    is_asc ==> (forall|k: int| i as int <= k < j as int ==> seq_i8_to_int(v@)[sel as int] <= seq_i8_to_int(v@)[k]),
                    !is_asc ==> (forall|k: int| i as int <= k < j as int ==> seq_i8_to_int(v@)[sel as int] >= seq_i8_to_int(v@)[k]),
                decreases n - j
            {
                if is_asc {
                    if v[j] < v[sel] {
                        sel = j;
                    }
                } else {
                    if v[j] > v[sel] {
                        sel = j;
                    }
                }
                j += 1;
            }
            // manual swap to avoid complex &mut borrow of Vec::swap
            let tmp = v[sel];
            v[sel] = v[i];
            v[i] = tmp;
            i += 1;
        }
    }
    v
}

// </vc-code>


}

fn main() {}