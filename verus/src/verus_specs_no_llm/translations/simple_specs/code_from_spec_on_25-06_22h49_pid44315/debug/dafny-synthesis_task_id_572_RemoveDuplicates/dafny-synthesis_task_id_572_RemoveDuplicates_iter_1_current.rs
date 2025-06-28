use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RemoveDuplicates(a: Vec<int>) -> (result: Seq<int>)
    ensures
        forall|x: int| result.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
{
    let mut result = Vec::new();
    let mut k = 0;
    
    while k < a.len()
        invariant
            0 <= k <= a.len(),
            forall|x: int| result@.contains(x) ==> exists|i: int| 0 <= i < k && a[i] == x,
            forall|i: int| 0 <= i < k && (exists|j: int| 0 <= j < i && a[j] == a[i]) ==> !result@.contains(a[i]),
            forall|i: int| 0 <= i < k && (forall|j: int| 0 <= j < i ==> a[j] != a[i]) ==> result@.contains(a[i]),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
    {
        let mut found = false;
        let mut m = 0;
        
        while m < k
            invariant
                0 <= m <= k,
                found <==> exists|j: int| 0 <= j < m && a[j] == a[k],
                k < a.len()
        {
            if a[m] == a[k] {
                found = true;
            }
            m = m + 1;
        }
        
        if !found {
            result.push(a[k]);
        }
        k = k + 1;
    }
    
    result@
}

}