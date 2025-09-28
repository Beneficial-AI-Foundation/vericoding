// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn select(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<i8>>, default: i8) -> (result: Vec<i8>)
    requires 
        condlist.len() == choicelist.len(),
        condlist.len() > 0 ==> (forall|i: int| 0 <= i < condlist.len() ==> #[trigger] condlist[i].len() == condlist[0].len()),
        choicelist.len() > 0 ==> (forall|i: int| 0 <= i < choicelist.len() ==> #[trigger] choicelist[i].len() == choicelist[0].len()),
        condlist.len() > 0 && choicelist.len() > 0 ==> condlist[0].len() == choicelist[0].len(),
    ensures
        condlist.len() == 0 ==> result.len() == 0,
        condlist.len() > 0 ==> result.len() == condlist[0].len(),
        forall|i: int| 0 <= i < result.len() ==> {
            (exists|j: int| 0 <= j < condlist.len() && condlist[j][i] == true && 
                #[trigger] result[i] == choicelist[j][i] &&
                (forall|j_prime: int| 0 <= j_prime < j ==> #[trigger] condlist[j_prime][i] == false)) ||
            (forall|j: int| 0 <= j < condlist.len() ==> #[trigger] condlist[j][i] == false && result[i] == default)
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix Vec indexing in invariants by using (condlist@[jj])@[i] instead of condlist@[jj]@[i] and cast i to usize in runtime */{
    if condlist.len() == 0 {
        let result: Vec<i8> = Vec::new();
        result
    } else {
        let n = condlist[0].len();
        let mut result: Vec<i8> = Vec::with_capacity(n as usize);
        let mut i = 0;
        while i < n
            invariant
                result.len() == i,
                forall|k: int| 0 <= k < i ==> {
                    (exists|j: int| 0 <= j < condlist.len() && (condlist@[j])@[k] == true &&
                        (forall|j_prime: int| 0 <= j_prime < j ==> (condlist@[j_prime])@[k] == false) &&
                        result@[k] == (choicelist@[j])@[k])
                    ||
                    (forall|j: int| 0 <= j < condlist.len() ==> (condlist@[j])@[k] == false && result@[k] == default)
                },
            decreases n - i
        {
            let mut val = default;
            let mut found = false;
            let mut j = 0;
            while j < condlist.len()
                invariant
                    0 <= j <= condlist.len(),
                    !found ==> (forall|jj: int| 0 <= jj < j ==> (condlist@[jj])@[i] == false),
                    found ==> (exists|jj: int| 0 <= jj < j && (condlist@[jj])@[i] == true &&
                        val == (choicelist@[jj])@[i] &&
                        (forall|j_prime: int| 0 <= j_prime < jj ==> (condlist@[j_prime])@[i] == false)),
                decreases condlist.len() - j
            {
                if !found && condlist[j][i as usize] {
                    val = choicelist[j][i as usize];
                    found = true;
                }
                j = j + 1;
            }
            result.push(val);
            i = i + 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}