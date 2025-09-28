// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(arr: Seq<int>) -> bool {
    true
}

spec fn distinct_non_zero_count(arr: Seq<int>) -> int {
    Set::<int>::new(|x: int| arr.contains(x) && x != 0).len() as int
}
// </vc-preamble>

// <vc-helpers>
spec fn vec_to_seq_int(arr: Vec<i8>) -> Seq<int> {
    arr@.map(|i, x| x as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Vec<i8>) -> (result: i8)
    requires 
        valid_input(vec_to_seq_int(arr))
    ensures 
        result >= 0,
        result as int <= arr@.len(),
        result as int == distinct_non_zero_count(vec_to_seq_int(arr))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Replaced Vec<bool> with Map<int, bool> to avoid while loop in proof block and fixed compilation error */
    let mut seen: Map<int, bool> = Map::empty();
    let mut count: int = 0;
    let mut i: int = 0;
    let len_int = arr.len() as int;
    while i < len_int
        invariant
            0 <= i <= len_int,
            0 <= count <= i,
            Map::dom(seen) == Set::new(|x: int| 0 <= x < 256 && exists |j: int| 0 <= j < i && (arr@[j] as int + 128) == x && arr@[j] != 0 && forall |k: int| 0 <= k < j ==> (arr@[k] as int + 128) != x || arr@[k] == 0),
            count == distinct_non_zero_count(vec_to_seq_int(arr).take(i))
        decreases len_int - i
    {
        let foc_i8 = arr@[i as usize];
        if foc_i8 != 0 {
            let idx = foc_i8 as int + 128;
            if !seen.contains_key(idx) {
                count = count + 1;
                seen = seen.insert(idx, true);
            }
        }
        i = i + 1;
    }
    proof {
        assert(count == distinct_non_zero_count(vec_to_seq_int(arr)));
    }
    count as i8
}
// </vc-code>


}

fn main() {}