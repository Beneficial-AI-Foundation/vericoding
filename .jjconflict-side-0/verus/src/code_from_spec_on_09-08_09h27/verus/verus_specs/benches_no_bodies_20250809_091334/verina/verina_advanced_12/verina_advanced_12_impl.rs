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
    let n = lst.len();
    
    for i in 0..n
        invariant 
            forall|a: int, b: int| 0 <= a < i && a < b < n ==> lst@[a] != lst@[b]
    {
        for j in (i + 1)..n
            invariant
                i < n,
                forall|a: int, b: int| 0 <= a < i && a < b < n ==> lst@[a] != lst@[b],
                forall|b: int| (i + 1) <= b < j ==> lst@[i as int] != lst@[b]
        {
            if lst[i] == lst[j] {
                return lst[i];
            }
        }
    }
    
    -1
}

}

fn main() {}