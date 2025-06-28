use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn compute_values(n: int) -> (x: int, m: int)
    requires
        n > 0
    ensures
        (n <= 0) || (0 <= m && m < n)
{
    let x = 0;
    let m = 0;
    
    (x, m)
}

}

The issue was likely with the excessive proof assertions. In Verus, when the logic is straightforward enough, it's often better to let the SMT solver figure out the proof automatically rather than adding manual assertions that might confuse the verification process.

The key insight is:
6. Therefore `(n <= 0) || (0 <= m && m < n)` is true

The simplified version should verify correctly without the manual assertions.