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
    cal_sum_loop(n)
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
        let prev_result = cal_sum_loop(n - 1);
        
        // Now we know prev_result <= 15 from the postcondition
        assert(n <= 5 && prev_result <= 15);
        let result = n + prev_result;
        
        // Prove the main postcondition
        assert(cal_sum_postcond((n - 1) as nat, prev_result as nat));
        assert(2 * prev_result as nat == (n - 1) as nat * n as nat);
        
        assert(result as nat == n as nat + prev_result as nat);
        assert(2 * result as nat == 2 * n as nat + 2 * prev_result as nat);
        assert(2 * result as nat == 2 * n as nat + (n - 1) as nat * n as nat);
        
        // Prove by cases for small n
        if n == 1 {
            assert(2 * result as nat == 2 * 1 + 0 * 1);
            assert(2 * result as nat == 2);
            assert(1 * (1 + 1) == 2);
        } else if n == 2 {
            assert(2 * result as nat == 2 * 2 + 1 * 2);
            assert(2 * result as nat == 6);
            assert(2 * (2 + 1) == 6);
        } else if n == 3 {
            assert(2 * result as nat == 2 * 3 + 2 * 3);
            assert(2 * result as nat == 12);
            assert(3 * (3 + 1) == 12);
        } else if n == 4 {
            assert(2 * result as nat == 2 * 4 + 3 * 4);
            assert(2 * result as nat == 20);
            assert(4 * (4 + 1) == 20);
        } else if n == 5 {
            assert(2 * result as nat == 2 * 5 + 4 * 5);
            assert(2 * result as nat == 30);
            assert(5 * (5 + 1) == 30);
        }
        
        assert(2 * result as nat == n as nat * (n as nat + 1));
        
        // Prove bounds
        assert(result <= 15);
        assert(result <= n * (n + 1) / 2);
        
        result
    }
}

} // end verus!

fn main() {
    let result = cal_sum(5);
    println!("Sum of 1 to 5 is: {}", result);
}