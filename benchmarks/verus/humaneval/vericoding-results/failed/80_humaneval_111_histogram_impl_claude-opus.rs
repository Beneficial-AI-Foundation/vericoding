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
    /* code modified by LLM (iteration 5): Remove proof block around while loop to fix compilation error */
    let ghost mut biggest = Map::<int, int>::empty();
    let ghost mut i: int = 0;
    
    while i < a@.len()
        invariant
            0 <= i <= a@.len(),
            forall|k: int| 0 <= k < i && biggest.dom().contains(a@[k] as int) ==>
                #[trigger] biggest[a@[k] as int] == Set::new(|j: int| 0 <= j < a@.len() && a@[j] as int == a@[k] as int).len(),
    {
        let val_int = a@[i] as int;
        if !biggest.dom().contains(val_int) {
            let count: nat = Set::new(|j: int| 0 <= j < a@.len() && a@[j] as int == val_int).len();
            biggest = biggest.insert(val_int, count as int);
        }
        i = i + 1;
    }
    
    biggest
}
// </vc-code>


}

fn main() {}