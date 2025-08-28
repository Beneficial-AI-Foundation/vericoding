use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn first_occurrence(a: &[i32], x: i32) -> int {
    if exists|i: int| 0 <= i < a.len() && a[i] == x {
        choose|i: int| 0 <= i < a.len() && a[i] == x && (forall|j: int| 0 <= j < i ==> a[j] != x)
    } else {
        -1
    }
}

spec fn appears_before(a: &[i32], x: i32, y: i32) -> bool {
    let first_x = first_occurrence(a, x);
    let first_y = first_occurrence(a, y);
    first_x >= 0 && first_y >= 0 && first_x < first_y
}

proof fn lemma_first_occurrence_correct(a: &[i32], x: i32)
    requires exists|i: int| 0 <= i < a.len() && a[i] == x
    ensures
        0 <= first_occurrence(a, x) < a.len(),
        a@[first_occurrence(a, x) as int] == x,
        forall|j: int| 0 <= j < first_occurrence(a, x) ==> a@[j] != x
{
    let idx = first_occurrence(a, x);
    assert(0 <= idx < a.len() && a@[idx] == x && (forall|j: int| 0 <= j < idx ==> a@[j] != x));
}

proof fn lemma_contains_preserved(result: &Vec<i32>, a: &[i32], x: i32)
    requires
        forall|y: i32| result@.contains(y) ==> exists|i: int| 0 <= i < a.len() && a@[i] == y,
        exists|i: int| 0 <= i < a.len() && a@[i] == x,
        !result@.contains(x)
    ensures
        forall|y: i32| result@.push(x).contains(y) <==> exists|i: int| 0 <= i < a.len() && a@[i] == y
{
    assert forall|y: i32| result@.push(x).contains(y) <==> exists|i: int| 0 <= i < a.len() && a@[i] == y by {
        if result@.push(x).contains(y) {
            if result@.contains(y) {
                assert(exists|i: int| 0 <= i < a.len() && a@[i] == y);
            } else {
                assert(y == x);
                assert(exists|i: int| 0 <= i < a.len() && a@[i] == y);
            }
        }
        if exists|i: int| 0 <= i < a.len() && a@[i] == y {
            if y == x {
                assert(result@.push(x).contains(y));
            } else {
                assert(result@.contains(y));
                assert(result@.push(x).contains(y));
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: i32| result@.contains(x) <==> exists|j: int| 0 <= j < i && a@[j] == x && (forall|k: int| 0 <= k < j ==> a@[k] != x),
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result@[p] != result@[q]
        decreases a.len() - i
    {
        let current = a[i];
        let mut found = false;
        let mut j: usize = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found <==> exists|k: int| 0 <= k < j && result@[k] == current,
                forall|x: i32| result@.contains(x) <==> exists|k: int| 0 <= k < i && a@[k] == x && (forall|l: int| 0 <= l < k ==> a@[l] != x),
                forall|p: int, q: int| 0 <= p < q < result.len() ==> result@[p] != result@[q]
            decreases result.len() - j
        {
            if result[j] == current {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            proof {
                assert(!result@.contains(current));
                assert(forall|k: int| 0 <= k < i ==> a@[k] != current);
            }
            result.push(current);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}