use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_palindrome_recursive(x: Seq<char>, start: nat, end_idx: nat) -> (result: bool)
  requires
    start <= end_idx + 1,
    end_idx < x.len(),
  ensures
    result <==> (forall|i: nat| start <= i <= end_idx ==> #[trigger] x.index(i as int) == x.index((x.len() - (i + 1)) as int)),
{
    if start >= end_idx {
        true
    } else {
        if x.index(start as int) != x.index((x.len() - (start + 1)) as int) {
            false
        } else {
            is_palindrome_recursive(x, (start + 1) as nat, (end_idx - 1) as nat)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
  ensures result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - i - 1])
// </vc-spec>
// <vc-code>
{
    let n = x.len();
    if n == (0 as nat) {
        true
    } else {
        let mut i: nat = 0;
        let mut j: nat = (n - 1) as nat;
        let mut result: bool = true;

        while i < j && result
            invariant
                0 <= i,
                i <= j + 1,
                j < n,
                result == (forall|k: nat| 0 <= k < i ==> #[trigger] x.index(k as int) == x.index((n - (k + 1)) as int)),
            decreases j - i
        {
            if x.index(i as int) != x.index(j as int) {
                result = false;
            }
            i = (i + 1) as nat;
            j = (j - 1) as nat;
        }
        result
    }
}
// </vc-code>

fn main() {}

}