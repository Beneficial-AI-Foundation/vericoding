use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
  ensures result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - i - 1])
// </vc-spec>
// <vc-code>
{
    if x.len() == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < x.len() / 2
        invariant
            0 <= i <= x.len() / 2,
            forall|j: int| 0 <= j < i ==> #[trigger] x[j] == x[x.len() - j - 1]
    {
        if x[i as int] != x[x.len() - i as int - 1] {
            assert(x[i as int] != x[x.len() - i as int - 1]);
            return false;
        }
        i += 1;
    }
    
    assert(forall|j: int| 0 <= j < x.len() / 2 ==> #[trigger] x[j] == x[x.len() - j - 1]);
    
    proof {
        assert(forall|k: int| 0 <= k < x.len() ==> {
            if k < x.len() / 2 {
                x[k] == x[x.len() - k - 1]
            } else if k >= x.len() / 2 {
                let mirror_k = x.len() - k - 1;
                mirror_k < x.len() / 2 && x[mirror_k] == x[x.len() - mirror_k - 1] && x.len() - mirror_k - 1 == k
            } else {
                true
            }
        });
    }
    
    true
}
// </vc-code>

fn main() {}

}