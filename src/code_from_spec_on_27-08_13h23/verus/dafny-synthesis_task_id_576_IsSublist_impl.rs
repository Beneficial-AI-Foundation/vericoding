use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn seq_equal_subrange(sub: Seq<int>, main: Seq<int>, start: int, end: int)
    requires
        0 <= start <= main.len(),
        end <= main.len(),
        start <= end,
        end - start == sub.len(),
        forall|k: int| 0 <= k < sub.len() ==> sub[k] == main[start + k],
    ensures
        sub =~= main.subrange(start, end)
{
    assert(sub.len() == end - start);
    assert(forall|k: int| 0 <= k < sub.len() ==> sub[k] == main.subrange(start, end)[k]);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
{
    if sub.len() > main.len() {
        return false;
    }

    let mut i: int = 0;
    while i <= main.len() - sub.len()
        invariant
            0 <= i <= main.len() - sub.len() + 1,
            forall|k: int| 0 <= k < i ==> !sub =~= main.subrange(k, k + sub.len()),
    {
        let mut matches = true;
        let mut j: int = 0;
        while j < sub.len()
            invariant
                0 <= i <= main.len() - sub.len(),
                0 <= j <= sub.len(),
                matches ==> forall|k: int| 0 <= k < j ==> sub[k] == main[i + k],
        {
            if sub[j] != main[i + j] {
                matches = false;
                break;
            }
            j = j + 1;
        }

        if matches {
            proof {
                seq_equal_subrange(sub, main, i, i + sub.len());
            }
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {
}

}