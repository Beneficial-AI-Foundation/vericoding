use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_reverse_index<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i] == s.reverse()[s.len() as int - i - 1],
{
    assert(s.reverse()[s.len() as int - i - 1] == s[i]);
}

spec fn is_palindrome_spec(x: Seq<char>) -> bool {
    forall|i: int| 0 <= i < x.len() ==> x[i] == x[x.len() as int - i - 1]
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
  ensures result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - i - 1])
// </vc-spec>
// <vc-code>
{
    let n = x.len() as int;
    let mut i: int = 0;
    while i < n / 2
        invariant
            0 <= i <= n/2,
            forall|j: int| 0 <= j < i ==> #[trigger] x[j] == x[n - j - 1],
    {
        if x[i as usize] != x[(n - i - 1) as usize] {
            return false;
        }
        i += 1;
    }
    
    proof {
        if 0 <= n/2 < x.len() {
            lemma_seq_reverse_index(x, n/2);
        }
    }
    
    if n % 2 == 1 {
        assert(x[(n/2) as usize] == x[(n/2) as usize]);
    }
    
    proof {
        assert forall|j: int| 0 <= j < n/2 ==> x[j as usize] == x[(n - j - 1) as usize] by {
            if j < i {
                assert(x[j as usize] == x[(n - j - 1) as usize]);
            } else {
                assert(j >= i);
                assert(j < n/2);
            }
        };
        assert forall|j: int| n/2 <= j < n ==> x[j as usize] == x[(n - j - 1) as usize] by {
            let k = n - j - 1;
            assert(0 <= k < n/2);
            assert(x[k as usize] == x[(n - k - 1) as usize]);
            assert(n - k - 1 == j);
        };
    }
    
    true
}
// </vc-code>

fn main() {}

}