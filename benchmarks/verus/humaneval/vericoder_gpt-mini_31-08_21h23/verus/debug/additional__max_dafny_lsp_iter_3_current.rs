use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn le_le_lt_implies_le(a: int, b: int, c: int)
    requires a <= b && b < c
    ensures a <= c
{
    assert(a <= c);
}

proof fn not_gt_implies_le(a: int, b: int)
    requires !(a > b)
    ensures a <= b
{
    assert(a <= b);
}

proof fn invariant_step(a: &[i32], i: usize, old_ans: usize, new_ans: usize)
    requires old_ans < a.len()
    requires i < a.len()
    requires forall |k: int| 0 <= k && k < (i as int) ==> a[k] <= a[old_ans as int],
    requires if a[i as int] > a[old_ans as int] { new_ans == i } else { new_ans == old_ans },
    ensures forall |k: int| 0 <= k && k < (i as int) + 1 ==> a[k] <= a[new_ans as int]
{
    forall |k: int| requires 0 <= k && k < (i as int) + 1
    {
        if k < i as int {
            // for k < i, use the old invariant
            assert(a[k] <= a[old_ans as int]);
            if a[i as int] > a[old_ans as int] {
                // new_ans == i, and a[old_ans] < a[i], so transitively a[k] <= a[i]
                le_le_lt_implies_le(a[k], a[old_ans as int], a[i as int]);
                assert(a[k] <= a[new_ans as int]);
            } else {
                // new_ans == old_ans
                assert(a[k] <= a[new_ans as int]);
            }
        } else {
            // k == i
            if a[i as int] > a[old_ans as int] {
                // new_ans == i, and a[i] <= a[i]
                assert(a[k] <= a[new_ans as int]);
            } else {
                // not (a[i] > a[old_ans]) implies a[i] <= a[old_ans]
                not_gt_implies_le(a[i as int], a[old_ans as int]);
                assert(a[k] <= a[new_ans as int]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    assert(n > 0);
    let mut i: usize = 1;
    let mut ans: usize = 0;
    while i < n
        invariant ans < n,
        invariant i <= n,
        invariant forall |k: int| 0 <= k && k < (i as int) ==> #[trigger] a[k] <= a[ans as int],
        decreases n - i
    {
        let old_ans = ans;
        if a[i as int] > a[ans as int] {
            ans = i;
        }
        proof {
            invariant_step(a, i, old_ans, ans);
        }
        i = i + 1;
    }
    ans
}
// </vc-code>

fn main() {}
}