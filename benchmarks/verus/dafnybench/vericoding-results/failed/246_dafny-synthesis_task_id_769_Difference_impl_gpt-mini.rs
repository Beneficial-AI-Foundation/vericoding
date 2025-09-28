use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j),
// </vc-spec>
// <vc-code>
{
    let mut diff: Seq<int> = Seq::empty();
    let mut i: nat = 0;
    while i < a.len()
        invariant i <= a.len()
        invariant forall|x: int| #[trigger] (diff.contains(x) <==> (exists|k: nat| k < i && a.index(k) == x && !b.contains(x)))
        invariant forall|p: nat, q: nat| p < q && q < diff.len() ==> diff.index(p) != diff.index(q)
    {
        let ai = a.index(i);
        if !b.contains(ai) && !diff.contains(ai) {
            let old_diff = diff;
            diff = diff + seq![ai];
            proof {
                // old uniqueness holds by invariant
                assert(forall|p: nat, q: nat| p < q && q < old_diff.len() ==> old_diff.index(p) != old_diff.index(q));
                // show new contains relation
                assert(forall|x: int|
                    diff.contains(x) <==> (old_diff.contains(x) || x == ai)
                );
                // relate old existence to new existence with k < i+1
                assert(forall|x: int|
                    (old_diff.contains(x) || x == ai) <==> (exists|k: nat| k < i+1 && a.index(k) == x && !b.contains(x))
                );
                // uniqueness for new diff: any duplicate involving ai impossible because ai not in old_diff
                assert(!old_diff.contains(ai));
                assert(forall|p: nat, q: nat|
                    p < q && q < diff.len() ==> diff.index(p) != diff.index(q)
                );
                // combine to get the needed invariant for i+1
                assert(forall|x: int| diff.contains(x) <==> (exists|k: nat| k < i+1 && a.index(k) == x && !b.contains(x)));
            }
        } else {
            let old_diff = diff;
            proof {
                assert(old_diff == diff);
                assert(forall|x: int|
                    (exists|k: nat| k < i+1 && a.index(k) == x && !b.contains(x)) <==>
                    ((exists|k: nat| k < i && a.index(k) == x && !b.contains(x)) ||
                     (a.index(i) == x && !b.contains(x)))
                );
                // From the else branch, if a.index(i) == x && !b.contains(x) then diff.contains(x) must already hold.
                assert(forall|x: int|
                    (a.index(i) == x && !b.contains(x)) ==> old_diff.contains(x)
                );
                assert(forall|x: int|
                    (exists|k: nat| k < i+1 && a.index(k) == x && !b.contains(x)) <==>
                    (exists|k: nat| k < i && a.index(k) == x && !b.contains(x))
                );
                assert(forall|x: int|
                    diff.contains(x) <==> (exists|k: nat| k < i+1 && a.index(k) == x && !b.contains(x))
                );
            }
        }
        i = i + 1;
    }
    diff
}
// </vc-code>

fn main() {}

}