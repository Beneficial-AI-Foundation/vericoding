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
/* code modified by LLM (iteration 5): moved entire map construction to proof block */
    let mut result: BiggestMap;
    proof {
        result = Map::new();
        let mut i: int = 0;
        while i < a@.len()
            invariant
                result.dom() == Set::new(|x: int| exists|j: int| 0 <= j < i && a@[j] as int == x),
                forall|x: int| result.dom().contains(x) ==> 
                    #[trigger] result[x] == Set::new(|j: int| 0 <= j < i && a@[j] as int == x).len(),
            decreases (a@.len()) - i,
        {
            let x = a@[i] as int;
            let old_count = if result.contains_key(x) { result[x] } else { 0 };
            result = result.insert(x, old_count + 1);
            i += 1;
        }
    }
    result
// </vc-code>


}

fn main() {}