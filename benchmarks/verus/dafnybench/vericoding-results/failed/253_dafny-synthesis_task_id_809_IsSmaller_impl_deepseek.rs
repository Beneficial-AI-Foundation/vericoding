use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn is_smaller_lemma(a: Seq<int>, b: Seq<int>, i: int) 
    requires 
        0 <= i < a.len(),
        a.len() == b.len(),
    ensures 
        a[i] <= b[i] ==> (exists|j: int| 0 <= j < a.len() && a[j] <= b[j])
{
}

proof fn forall_implies_not_exists(a: Seq<int>, b: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        (forall|i: int| 0 <= i < a.len() ==> a[i] > b[i]) ==>
        !(exists|i: int| 0 <= i < a.len() && a[i] <= b[i])
{
}

proof fn exists_implies_not_forall(a: Seq<int>, b: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        (exists|i: int| 0 <= i < a.len() && a[i] <= b[i]) ==>
        !(forall|i: int| 0 <= i < a.len() ==> a[i] > b[i])
{
}
// </vc-helpers>

// <vc-spec>
fn is_smaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires 
        a.len() == b.len(),
    ensures 
        result <==> forall|i: int| 0 <= i < a.len() ==> a[i] > b[i],
        !result <==> exists|i: int| 0 <= i < a.len() && a[i] <= b[i],
// </vc-spec>
// <vc-code>
{
    proof {
        let len = a.len();
    }
    let mut index: usize = 0;
    let len = a.len();
    while index < len
        invariant
            0 <= index <= len,
            forall|j: int| 0 <= j < index as int ==> a[j] > b[j],
        decreases len - index,
    {
        if a[index] <= b[index] {
            return false;
        }
        index = index + 1;
    }
    proof { 
        forall_implies_not_exists(a, b);
        exists_implies_not_forall(a, b);
    }
    true
}
// </vc-code>

fn main() {}

}