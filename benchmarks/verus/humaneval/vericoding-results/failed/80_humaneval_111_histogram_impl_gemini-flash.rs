// <vc-preamble>
use vstd::prelude::*;

verus! {

type BiggestMap = Map<int, int>;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed incorrect keyword `pure` to `pure fn` */
pure fn nat_eq(x: nat, y: nat) -> bool {
    x == y
}
// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>) -> (biggest: BiggestMap)
  ensures forall|i: int| 0 <= i < a@.len() && biggest.dom().contains(a@[i] as int) ==>
    #[trigger] biggest[a@[i] as int] == Set::new(|j: int| 0 <= j < a@.len() && a@[j] as int == a@[i] as int).len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed unnecessary ghost variable and added ensures clause for loop */
{
    let mut counts: BiggestMap = Map::empty();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            forall|k: int| (#counts).dom().contains(k) ==> (#counts)[k] == Set::new(|j: int| 0 <= j < i && a@[j] as int == k).len(),
            forall|k: int| !(#counts).dom().contains(k) ==> forall|j: int| !(0 <= j < i && a@[j] as int == k),
        decreases a.len() - i
    {
        let val = a@[i] as int;
        let current_count = if counts.dom().contains(val) { counts[val] } else { 0 };
        counts = counts.insert(val, current_count + 1);
        i = i + 1;
    }
    counts
}
// </vc-code>


}

fn main() {}