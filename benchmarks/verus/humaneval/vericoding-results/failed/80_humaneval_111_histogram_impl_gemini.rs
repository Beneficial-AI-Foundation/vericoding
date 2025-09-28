// <vc-preamble>
use vstd::prelude::*;

verus! {

type BiggestMap = Map<int, int>;
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>) -> (biggest: BiggestMap)
  ensures forall|i: int| 0 <= i < a@.len() && biggest.dom().contains(a@[i] as int) ==>
    #[trigger] biggest[a@[i] as int] == Set::new(|j: int| 0 <= j < a@.len() && a@[j] as int == a@[i] as int).len()
// </vc-spec>
// <vc-code>
{
    let mut biggest: BiggestMap = Map::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| biggest.dom().contains(k) ==> (exists|j: int| 0 <= j < i && a@[j] as int == k),
            forall|j: int| 0 <= j < i ==> biggest.dom().contains(a@[j] as int),
            forall|k: int| biggest.dom().contains(k) ==>
                #[trigger] biggest[k] == Set::new(|j: int| 0 <= j < i && a@[j] as int == k).len(),
        decreases a.len() - i
    {
        let val = a[i] as int;
        if biggest.dom().contains(val) {
            proof {
                let s_old = Set::new(|j: int| 0 <= j < i && a@[j] as int == val);
                let s_new = Set::new(|j: int| 0 <= j < i + 1 && a@[j] as int == val);
                assert(s_new =~= s_old.insert(i as int));
                assert(!s_old.contains(i as int));
                vstd::set_lib::lemma_len_insert(s_old, i as int);
            }
            biggest = biggest.insert(val, biggest[val] + 1);
        } else {
            proof {
                let s_old = Set::new(|j: int| 0 <= j < i && a@[j] as int == val);
                assert forall |j: int| 0 <= j < i implies a@[j] as int != val by {
                    if a@[j] as int == val {
                        assert(biggest.dom().contains(a@[j] as int));
                        assert(false);
                    }
                }
                assert(s_old.is_empty());

                let s_new = Set::new(|j: int| 0 <= j < i + 1 && a@[j] as int == val);
                assert(s_new =~= s_old.insert(i as int));
                vstd::set_lib::lemma_len_insert(s_old, i as int);
            }
            biggest = biggest.insert(val, 1);
        }
        i = i + 1;
    }
    biggest
}
// </vc-code>


}

fn main() {}