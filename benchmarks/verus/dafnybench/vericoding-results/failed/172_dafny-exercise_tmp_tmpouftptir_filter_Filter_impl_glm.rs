use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
// </vc-spec>
// <vc-code>
{
    let mut result_set = Set::<char>::empty();
    let mut i: int = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            forall |x: char| 
                result_set.contains(x) <==> 
                    (exists |j: int| 0 <= j < i && (#[trigger] a[j]) == x) && b.contains(x)
    {
        let x = a[i];
        if b.contains(x) {
            result_set = result_set.insert(x);
        }
        i = i + 1;
    }
    result_set
}
// </vc-code>

fn main() {
}

}