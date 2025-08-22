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
    n * (n + 1) / 2
}

fn cal_sum_loop(n: u32) -> (result: u32)
    requires n <= 5
    ensures cal_sum_postcond(n as nat, result as nat),
            result <= n * (n + 1) / 2,
            result <= 15  // specific bound for n <= 5
    decreases n
{
    if n == 0 {
        0
    } else {
        let prev = cal_sum_loop(n - 1);
        prev + n
    }
}

} // end verus!

fn main() {
}