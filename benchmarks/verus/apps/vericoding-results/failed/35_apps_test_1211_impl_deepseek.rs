// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, a: Seq<int>) -> bool {
    k > 0 && a.len() == k && (forall|i: int| 0 <= i < k ==> #[trigger] a[i] > 0) && n >= 0
}

spec fn hamsters_transported(n: int, capacity: int) -> int {
    if capacity > 0 {
        capacity * (n / capacity)
    } else {
        0
    }
}

spec fn optimal_solution(n: int, a: Seq<int>, box_type: int, num_boxes: int) -> bool {
    valid_input(n, a.len() as int, a) &&
    1 <= box_type <= a.len() &&
    num_boxes == n / a[box_type - 1] &&
    forall|i: int| 0 <= i < a.len() ==> #[trigger] hamsters_transported(n, a[box_type - 1]) >= #[trigger] hamsters_transported(n, a[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed sequence element access syntax */
proof fn lemma_div_ordering(a: int, b: int, n: int)
    requires
        a > 0,
        b > 0,
        n >= 0,
        a <= b,
    ensures
        hamsters_transported(n, a) >= hamsters_transported(n, b),
    decreases n,
{
    if n > 0 {
        lemma_div_ordering(a, b, n - 1);
    }
}

proof fn lemma_div_properties(n: int, d: int)
    requires
        n >= 0,
        d > 0,
    ensures
        hamsters_transported(n, d) == d * (n / d),
        hamsters_transported(n, d) <= n,
    decreases n,
{
    if n > 0 {
        lemma_div_properties(n - 1, d);
    }
}

proof fn lemma_positive_sequence_elements(a: Seq<int>, k: int)
    requires
        k > 0,
        a.len() == k,
        forall|i: int| 0 <= i < k ==> #[trigger] a[i] > 0,
    ensures
        forall|i: int| 0 <= i < k ==> a[i] > 0,
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: (i8, i8))
    requires valid_input(n as int, k as int, a@.map(|i, x: i8| x as int))
    ensures ({
        let (box_type, num_boxes) = result;
        1 <= box_type <= k &&
        num_boxes >= 0 &&
        optimal_solution(n as int, a@.map(|i, x: i8| x as int), box_type as int, num_boxes as int)
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed sequence indexing syntax and ghost block structure */
    let mut best_type: i8 = 0;
    let mut max_transported: i8 = -1;
    let mut i: i8 = 0;
    
    let pure_a = a@.map(|x: i8| x as int);
    
    while i < k
        invariant
            0 <= i <= k,
            forall|j: int| 0 <= j < i ==> {
                let ghost_cap = pure_a[j as int];
                ghost { hamsters_transported(n as int, ghost_cap) } as i8 <= max_transported
            },
            best_type >= 0,
            max_transported >= -1,
        decreases k as int - i as int,
    {
        let capacity = a[i as usize] as int;
        let transported: i8;
        
        {
            let transported_spec = hamsters_transported(n as int, capacity);
            transported = transported_spec as i8;
        }
        
        if transported > max_transported {
            max_transported = transported;
            best_type = i + 1;
        }
        
        i = i + 1;
    }
    
    let num_boxes = n / a[(best_type - 1) as usize];
    (best_type, num_boxes)
}
// </vc-code>


}

fn main() {}