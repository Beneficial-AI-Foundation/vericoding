// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 &&
    a.len() == n &&
    (forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a[i] <= n) &&
    (forall|i: int, j: int| 0 <= i < j < n ==> a[i] != a[j])
}

spec fn valid_output(n: int, result: int) -> bool {
    0 <= result <= n
}

spec fn reversed_array(a: Seq<int>) -> Seq<int>
    recommends a.len() >= 1
{
    Seq::new(a.len(), |i: int| a[a.len() - 1 - i])
}

spec fn has_increasing_pair(ar: Seq<int>) -> bool {
    exists|i: int| 1 <= i < ar.len() && #[trigger] ar[i] > ar[i-1]
}

spec fn min_index(ar: Seq<int>, n: int) -> int {
    0
}

spec fn correct_result(n: int, a: Seq<int>) -> int
    recommends valid_input(n, a)
{
    let ar = reversed_array(a);
    if has_increasing_pair(ar) {
        let min_i = min_index(ar, n);
        n - min_i
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma function declaration syntax */
proof fn lemma_reversed_array_bounds(a: Seq<int>, i: int)
    requires
        a.len() >= 1,
        0 <= i < a.len()
    ensures
        0 <= a.len() - 1 - i < a.len()
{
}

proof fn lemma_reversed_array_access(a: Seq<int>, i: int)
    requires
        a.len() >= 1,
        0 <= i < a.len()
    ensures
        reversed_array(a)[i] == a[a.len() - 1 - i]
{
}

fn find_min_increasing_index(ar: Vec<i8>) -> (result: i8)
    requires
        ar.len() >= 1,
        ar.len() <= 127
    ensures
        0 <= result < ar.len(),
        result == 0 || ar[result as int] > ar[(result - 1) as int],
        forall|j: int| 1 <= j < result ==> ar[j] <= ar[j-1]
{
    let mut i = 1;
    while i < ar.len()
        invariant
            1 <= i <= ar.len(),
            forall|j: int| 1 <= j < i ==> ar[j] <= ar[j-1]
    {
        if ar[i] > ar[i-1] {
            return i as i8;
        }
        i += 1;
    }
    0
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures 
        valid_output(n as int, result as int) &&
        result as int == correct_result(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed indexing and proof structure */
    let mut ar: Vec<i8> = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            ar.len() == i,
            forall|j: int| 0 <= j < i ==> ar@[j] == a@[(n - 1 - j) as int]
    {
        ar.push(a[(n - 1 - i) as usize]);
        i += 1;
    }
    
    let mut found_increasing = false;
    let mut min_i = 0;
    
    i = 1;
    while i < n
        invariant
            1 <= i <= n,
            !found_increasing ==> forall|j: int| 1 <= j < i ==> ar@[j] <= ar@[j-1],
            found_increasing ==> (
                exists|k: int| 1 <= k < i && ar@[k] > ar@[k-1]
            )
    {
        if ar[i as usize] > ar[(i-1) as usize] {
            found_increasing = true;
            min_i = i;
            break;
        }
        i += 1;
    }
    
    if found_increasing {
        n - min_i
    } else {
        0
    }
}
// </vc-code>


}

fn main() {}