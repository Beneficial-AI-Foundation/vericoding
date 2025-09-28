use vstd::prelude::*;

verus! {

/**
 * Find odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
proof fn lemma_seq_contains_index(s: Seq<i32>, i: int)
    ensures
        0 <= i < s.len() ==> s.contains(s[i])
{
    if 0 <= i && i < s.len() {
        assert(exists|j: int| 0 <= j < s.len() && #[trigger] s[j] == s[i]) by {
            let j = i;
            assert(0 <= j && j < s.len());
            assert(s[j] == s[i]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &[i32]) -> (odd_list: Vec<i32>)
    // All numbers in the output are odd and exist in the input 
    ensures forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i] as int) && arr@.contains(odd_list[i])
    // All odd numbers in the input are in the output
    ensures forall|i: int| 0 <= i < arr.len() && is_odd(arr[i] as int) ==> odd_list@.contains(arr[i])
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant i <= arr.len()
        invariant forall|j: int| 0 <= j < res@.len() ==> is_odd(res@[j] as int) && arr@.contains(res@[j])
        invariant forall|k: int| 0 <= k < i as int && is_odd(arr@[k] as int) ==> res@.contains(arr@[k])
        decreases (arr.len() - i) as int
    {
        let x = arr[i];
        if is_odd(x as int) {
            let old_len: usize = res.len();
            res.push(x);
            proof {
                let ii: int = i as int;
                assert(0 <= ii && ii < arr@.len());
                assert(arr@[ii] == x);

                let ol: int = old_len as int;
                assert(0 <= ol && ol < res@.len());
                assert(res@[ol] == x);

                // New element is odd and in arr
                assert(is_odd(x as int));
                assert(arr@.contains(x)) by {
                    assert(exists|j: int| 0 <= j < arr@.len() && #[trigger] arr@[j] == x) by {
                        let j = ii;
                        assert(0 <= j && j < arr@.len());
                        assert(arr@[j] == x);
                    }
                }

                // Show the newly added odd element from arr is contained in res
                assert(res@[ol] == arr@[ii]);
                assert(res@.contains(arr@[ii])) by {
                    assert(exists|j: int| 0 <= j < res@.len() && #[trigger] res@[j] == arr@[ii]) by {
                        let j = ol;
                        assert(0 <= j && j < res@.len());
                        assert(res@[j] == arr@[ii]);
                    }
                }
            }
        }
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {}

}