use vstd::prelude::*;

verus! {

spec fn cal_sum_precond(n: nat) -> bool {
    true
}

spec fn cal_sum_postcond(n: nat, result: nat) -> bool {
    2 * result == n * (n + 1)
}

fn cal_sum(n: u32) -> (result: u32)
    requires cal_sum_precond(n as nat),
             n <= 5
    ensures cal_sum_postcond(n as nat, result as nat)
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn cal_sum_loop(n: u32) -> (result: u32)
    requires n <= 5
    ensures cal_sum_postcond(n as nat, result as nat),
            result <= n * (n + 1) / 2,
            result <= 15  // specific bound for n <= 5
    decreases n
{
    return 0;  // TODO: Remove this line and implement the function body
}

} // end verus!

fn main() {
    // TODO: Remove this comment and implement the function body
}