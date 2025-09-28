use vstd::prelude::*;

verus! {

/**
 * Find odd numbers from an array of numbers
 **/

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// <vc-helpers>
spec fn seq_contains_odd<T>(s: Seq<T>, n: T) -> bool 
where T: core::cmp::PartialEq
{
    exists|i: int| 0 <= i < s.len() && s[i] == n
}

proof fn lemma_odd_membership(s: Seq<i32>, n: i32)
    requires
        is_odd(n as int) && s.contains(n),
    ensures
        exists|i: int| 0 <= i < s.len() && is_odd(s[i] as int) && s[i] == n,
{
}

proof fn lemma_forall_odd_implies_exists(s: Seq<i32>, n: i32)
    requires
        is_odd(n as int) && s.contains(n),
    ensures
        seq_contains_odd(s, n),
{
}

proof fn lemma_contains_odd_implies_contains(s: Seq<i32>, n: i32)
    requires
        seq_contains_odd(s, n),
    ensures
        s.contains(n),
{
}

proof fn lemma_push_preserves_invariants(arr: Seq<i32>, odd_list: Seq<i32>, j: int, val: i32)
    requires
        0 <= j < arr.len(),
        forall|i: int| 0 <= i < odd_list.len() ==> is_odd(odd_list[i] as int) && arr.contains(odd_list[i]),
        forall|k: int| 0 <= k < j && is_odd(arr[k] as int) ==> seq_contains_odd(odd_list, arr[k]),
        is_odd(val as int) && val == arr[j],
    ensures
        forall|i: int| 0 <= i < odd_list.push(val).len() ==> is_odd(odd_list.push(val)[i] as int) && arr.contains(odd_list.push(val)[i]),
        forall|k: int| 0 <= k <= j && is_odd(arr[k] as int) ==> seq_contains_odd(odd_list.push(val), arr[k]),
{
    let new_list = odd_list.push(val);
    assert forall|i: int| 0 <= i < new_list.len() implies is_odd(new_list[i] as int) && arr.contains(new_list[i]) by {
        if i < odd_list.len() {
            assert(new_list[i] == odd_list[i]);
        } else {
            assert(i == odd_list.len());
            assert(new_list[i] == val);
            assert(arr.contains(val));
        }
    };
    assert forall|k: int| 0 <= k <= j && is_odd(arr[k] as int) implies seq_contains_odd(new_list, arr[k]) by {
        if k < j {
            assert(seq_contains_odd(odd_list, arr[k]));
            assert(seq_contains_odd(odd_list, arr[k]) ==> exists|idx: int| 0 <= idx < odd_list.len() && odd_list[idx] == arr[k]);
            if exists|idx: int| 0 <= idx < odd_list.len() && odd_list[idx] == arr[k] {
                assert(new_list[idx] == arr[k]);
                assert(0 <= idx < new_list.len());
                assert(seq_contains_odd(new_list, arr[k]));
            }
        } else {
            assert(k == j);
            assert(new_list[odd_list.len()] == val);
            assert(0 <= odd_list.len() < new_list.len());
            assert(seq_contains_odd(new_list, val));
        }
    };
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
  let mut odd_list: Vec<i32> = Vec::new();
  let mut j: usize = 0;
  while j < arr.len()
    invariant
        0 <= j <= arr.len(),
        forall|i: int| 0 <= i < odd_list@.len() ==> is_odd(odd_list@[i] as int) && arr@.contains(odd_list@[i]),
        forall|k: int| 0 <= k < j && is_odd(arr@[k] as int) ==> seq_contains_odd(odd_list@, arr@[k]),
  {
      let elem = arr[j];
      if is_odd(elem as int) {
          proof {
              lemma_push_preserves_invariants(arr@, odd_list@, j as int, elem);
          }
          odd_list.push(elem);
      }
      j = j + 1;
  }
  proof {
      assert forall|i: int| 0 <= i < arr.len() && is_odd(arr@[i] as int) implies odd_list@.contains(arr@[i]) by {
          let k = i;
          assert(0 <= k < arr.len() && is_odd(arr@[k] as int));
          assert(seq_contains_odd(odd_list@, arr@[k]));
          lemma_contains_odd_implies_contains(odd_list@, arr@[k]);
      };
  }
  odd_list
}
// </vc-code>

fn main() {}

}