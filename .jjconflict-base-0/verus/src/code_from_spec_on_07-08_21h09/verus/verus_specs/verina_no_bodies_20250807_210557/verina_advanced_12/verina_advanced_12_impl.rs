use vstd::prelude::*;

verus! {

spec fn first_duplicate_precond(lst: Seq<i32>) -> bool {
    true
}

spec fn first_duplicate_postcond(lst: Seq<i32>, result: i32) -> bool {
    (result == -1 ==> forall|i: int, j: int| 0 <= i < j < lst.len() ==> lst[i] != lst[j]) &&
    (result != -1 ==> exists|i: int, j: int| 0 <= i < j < lst.len() && lst[i] == result && lst[j] == result)
}

fn first_duplicate(lst: Vec<i32>) -> (result: i32)
    requires first_duplicate_precond(lst@)
    ensures first_duplicate_postcond(lst@, result)
{
    let mut i = 0;
    while i < lst.len()
        invariant 
            0 <= i <= lst.len(),
            forall|x: int, y: int| 0 <= x < y < i ==> lst@[x] != lst@[y]
        /* code modified by LLM (iteration 1): add decreases clause for termination */
        decreases lst.len() - i
    {
        let mut j = i + 1;
        while j < lst.len()
            invariant
                0 <= i < lst.len(),
                i + 1 <= j <= lst.len(),
                forall|k: int| i as int + 1 <= k < j ==> lst@[i as int] != lst@[k],
                forall|x: int, y: int| 0 <= x < y < i ==> lst@[x] != lst@[y]
            /* code modified by LLM (iteration 1): add decreases clause for inner loop termination */
            decreases lst.len() - j
        {
            if lst[i] == lst[j] {
                return lst[i];
            }
            j += 1;
        }
        i += 1;
    }
    -1
}

}

fn main() {}