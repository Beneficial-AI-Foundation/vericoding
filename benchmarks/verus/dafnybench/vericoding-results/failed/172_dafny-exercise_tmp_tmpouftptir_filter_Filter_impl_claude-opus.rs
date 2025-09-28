use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn filter(a: Seq<char>, b: Set<char>) -> (c: Set<char>)
    ensures forall|x: char| a.contains(x) && b.contains(x) <==> c.contains(x)
// </vc-spec>
// <vc-code>
{
    let mut result: Set<char> = Set::empty();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            forall|x: char| result.contains(x) <==> 
                (a.take(i as int).contains(x) && b.contains(x)),
    {
        let ch = a[i as int];  // Use a[i as int] instead of a@[i as int]
        if b.contains(ch) {
            result = result.insert(ch);
            
            proof {
                assert(a.take((i + 1) as int) =~= a.take(i as int).push(ch));
                assert(forall|x: char| #[trigger] result.insert(ch).contains(x) <==>
                    (x == ch || result.contains(x)));
                assert(forall|x: char| #[trigger] a.take((i + 1) as int).contains(x) <==>
                    (a.take(i as int).contains(x) || x == ch));
            }
        } else {
            proof {
                assert(a.take((i + 1) as int) =~= a.take(i as int).push(ch));
                assert(!b.contains(ch));
                assert(forall|x: char| #[trigger] a.take((i + 1) as int).contains(x) <==>
                    (a.take(i as int).contains(x) || x == ch));
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(a.take(a.len() as int) =~= a);
    }
    
    result
}
// </vc-code>

fn main() {
}

}