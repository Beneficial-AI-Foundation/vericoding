use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn symmetric_lemma(a: &[i32], i: int, j: int)
    requires
        0 <= i < a.len() as int,
        0 <= j < a.len() as int,
    ensures
        a@[i] == a@[j],
{
    // Trivial lemma for equality
}

proof fn symmetric_exists_lemma(a: &[i32], x: int)
    requires
        0 <= x < a.len() as int,
        a@[x] != a@[a.len() as int - x - 1],
    ensures
        exists|x: int| 0 <= x < a.len() as int && #[trigger] a@[x] != a@[a.len() as int - x - 1],
{
    assert(a@[x] != a@[a.len() as int - x - 1]);
}

proof fn symmetric_reflection_lemma(a: &[i32], x: int)
    requires
        0 <= x < a.len() as int,
    ensures
        a.len() as int - (a.len() as int - x - 1) - 1 == x,
{
    // This lemma establishes that reflection is an involution
}

proof fn range_lemma(n: int, x: int)
    requires
        n >= 0,
        n/2 <= x < n,
    ensures
        0 <= n - x - 1 < n/2,
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn symmetric(a: &[i32]) -> (flag: bool)
    ensures 
        flag == true ==> forall|x: int| 0 <= x < a.len() ==> #[trigger] a[x] == a[a.len() - x - 1],
        flag == false ==> exists|x: int| #[trigger] a[x] != a[a.len() - x - 1] && 0 <= x < a.len(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = 0;
    let mut flag = true;
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            flag == true ==> forall|j: int| 0 <= j < i as int ==> #[trigger] a@[j] == a@[n as int - j - 1],
            flag == false ==> exists|j: int| 0 <= j < i as int && #[trigger] a@[j] != a@[n as int - j - 1],
        decreases (n / 2) - i
    {
        let j_val = n - i - 1;
        assert(0 <= i < n) by { assert(i < n / 2); assert(n / 2 <= n); }
        assert(0 <= j_val < n) by { assert(i < n / 2); }
        
        if a[i] != a[j_val] {
            flag = false;
            proof {
                symmetric_exists_lemma(a, i as int);
            }
            break;
        }
        i += 1;
    }
    
    if flag == true {
        proof {
            assert forall|x: int| 0 <= x < n as int implies #[trigger] a@[x] == a@[n as int - x - 1] by {
                symmetric_reflection_lemma(a, x);
                if x < n as int / 2 {
                    // Already established by the loop invariant
                } else {
                    let y = n as int - x - 1;
                    assert(0 <= y < n as int / 2) by {
                        range_lemma(n as int, x);
                    };
                    assert(a@[y] == a@[n as int - y - 1]); // From loop invariant
                    assert(n as int - y - 1 == x); // By reflection lemma
                    assert(a@[y] == a@[x]); // Substitution
                }
            }
        }
    } else {
        // The loop invariant already ensures the existence
        proof {
            assert(exists|j: int| 0 <= j < i as int && a@[j] != a@[n as int - j - 1]);
            assert(i as int <= n as int / 2);
            assert_forall_by(|x: int| {
                requires(0 <= x < i as int);
                ensures(a@[x] != a@[n as int - x - 1] ==> 0 <= x < n as int && a@[x] != a@[n as int - x - 1]);
            });
        }
    }
    
    flag
}
// </vc-code>

fn main() {}

}