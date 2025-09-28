use vstd::prelude::*;

verus! {

// <vc-helpers>
//
// </vc-helpers>

// <vc-code>
{
    let n: int = s@.len();
    if n < 2 {
        return (false, ' ');
    }
    let mut i: int = 0;
    #[verifier::loop_isolation(false)]
    while i < n - 1
        invariant
            n == s@.len(),
            forall|k: int| 0 <= k < i ==> forall|l: int| k + 1 <= l < n ==> s@[k] != s@[l],
    {
        let mut j: int = i + 1;
        #[verifier::loop_isolation(false)]
        while j < n
            invariant
                n == s@.len(),
                i < n - 1,
                j >= i + 1,
                forall|k: int| 0 <= k < i ==> forall|l: int| k + 1 <= l < n ==> s@[k] != s@[l],
                forall|l: int| (i + 1) <= l < j ==> s@[i] != s@[l],
        {
            assert(i < n && j < n);
            let ci = s.chars().nth(i as usize).unwrap();
            let cj = s.chars().nth(j as usize).unwrap();
            if ci == cj {
                return (true, ci);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    (false, ' ')
}
// </vc-code>```
// </vc-helpers>

// <vc-spec>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures 
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 && 
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j]))
// </vc-spec>
// <vc-code>
//
// </vc-helpers>

// <vc-code>
{
    let n: int = s@.len();
    if n < 2 {
        return (false, ' ');
    }
    let mut i: int = 0;
    #[verifier::loop_isolation(false)]
    while i < n - 1
        invariant
            n == s@.len(),
            forall|k: int| 0 <= k < i ==> forall|l: int| k + 1 <= l < n ==> s@[k] != s@[l],
    {
        let mut j: int = i + 1;
        #[verifier::loop_isolation(false)]
        while j < n
            invariant
                n == s@.len(),
                i < n - 1,
                j >= i + 1,
                forall|k: int| 0 <= k < i ==> forall|l: int| k + 1 <= l < n ==> s@[k] != s@[l],
                forall|l: int| (i + 1) <= l < j ==> s@[i] != s@[l],
        {
            assert(i < n && j < n);
            let ci = s.chars().nth(i as usize).unwrap();
            let cj = s.chars().nth(j as usize).unwrap();
            if ci == cj {
                return (true, ci);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    (false, ' ')
}
// </vc-code>```
// </vc-code>

fn main() {}

}