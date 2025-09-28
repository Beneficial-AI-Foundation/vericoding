// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no helpers needed] */
// </vc-helpers>

// <vc-spec>
fn hermsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < c1.len() && 0 <= i < c2.len() ==> 
            result@[i] == c1@[i] - c2@[i],
        c1.len() > c2.len() ==> forall|i: int| 
            c2.len() <= i < c1.len() ==> result@[i] == c1@[i],
        c2.len() > c1.len() ==> forall|i: int| 
            c1.len() <= i < c2.len() ==> result@[i] == -c2@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [Added explicit context to loop invariants to resolve indexing errors.] */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let n1 = c1.len();
    let n2 = c2.len();

    if n1 >= n2 {
        while i < n2
            invariant
                n1 == c1.len(),
                n2 == c2.len(),
                n1 >= n2,
                i <= n2,
                result.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == c1@[j] - c2@[j],
            decreases n2 - i
        {
            assert(i < c1.len());
            assert(i < c2.len());
            let sub = c1[i] - c2[i];
            result.push(sub);
            i = i + 1;
        }

        while i < n1
            invariant
                n1 == c1.len(),
                n2 == c2.len(),
                n1 >= n2,
                n2 <= i && i <= n1,
                result.len() == i,
                forall|j: int| 0 <= j < n2 as int ==> #[trigger] result@[j] == c1@[j] - c2@[j],
                forall|j: int| n2 as int <= j < i as int ==> #[trigger] result@[j] == c1@[j],
            decreases n1 - i
        {
            assert(i < c1.len());
            result.push(c1[i]);
            i = i + 1;
        }
    } else { // n1 < n2
        while i < n1
            invariant
                n1 == c1.len(),
                n2 == c2.len(),
                n1 < n2,
                i <= n1,
                result.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == c1@[j] - c2@[j],
            decreases n1 - i
        {
            assert(i < c1.len());
            assert(i < c2.len());
            let sub = c1[i] - c2[i];
            result.push(sub);
            i = i + 1;
        }

        while i < n2
            invariant
                n1 == c1.len(),
                n2 == c2.len(),
                n1 < n2,
                n1 <= i && i <= n2,
                result.len() == i,
                forall|j: int| 0 <= j < n1 as int ==> #[trigger] result@[j] == c1@[j] - c2@[j],
                forall|j: int| n1 as int <= j < i as int ==> #[trigger] result@[j] == -c2@[j],
            decreases n2 - i
        {
            assert(i < c2.len());
            let neg = -c2[i];
            result.push(neg);
            i = i + 1;
        }
    }
    result
}
// </vc-code>


}
fn main() {}