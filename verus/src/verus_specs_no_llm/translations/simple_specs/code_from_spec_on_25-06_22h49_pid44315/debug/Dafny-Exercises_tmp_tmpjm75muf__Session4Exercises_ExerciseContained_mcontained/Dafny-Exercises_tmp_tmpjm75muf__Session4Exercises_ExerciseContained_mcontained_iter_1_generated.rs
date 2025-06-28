use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn strictSorted(s: Seq<int>) -> bool {
    forall |u, w| 0 <= u < w < s.len() ==> s.spec_index(u) < s.spec_index(w)
}

fn mcontained(v: Vec<int>, w: Vec<int>, n: int, m: int) -> (b: bool)
    requires
        n <= m && n >= 0,
        strictSorted(v.spec_index(..)),
        strictSorted(w.spec_index(..)),
        v.len() >= n && w.len() >= m
    ensures
        b == forall |k| 0 <= k < n ==> v.spec_index(k) in w.spec_index(..m)
{
    if n == 0 {
        return true;
    }
    
    let mut i: usize = 0; // index for v
    let mut j: usize = 0; // index for w
    
    while i < n && j < m
        invariant
            0 <= i <= n,
            0 <= j <= m,
            // All elements v[0..i] have been found in w[0..j]
            forall |k| 0 <= k < i ==> v.spec_index(k) in w.spec_index(..j),
            // If i < n, then v[i] > all elements in w[0..j]
            i < n ==> forall |l| 0 <= l < j ==> w.spec_index(l) < v.spec_index(i),
    {
        if v[i] == w[j] {
            i += 1;
            j += 1;
        } else if v[i] > w[j] {
            j += 1;
        } else {
            // v[i] < w[j], but all remaining elements in w are >= w[j] > v[i]
            // So v[i] cannot be found in w
            return false;
        }
    }
    
    i == n
}

}