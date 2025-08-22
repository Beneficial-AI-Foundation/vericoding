/*
You are climbing a staircase. It takes n steps to reach the top.

Each time you can either climb 1 or 2 steps. In how many distinct ways can you climb to the top?
*/

// Basic implementation of climbing stairs using dynamic programming
function climbStairs(n: nat): nat
{
    if n == 0 then 1
    else if n == 1 then 1  
    else if n == 2 then 2
    else climbStairs(n-1) + climbStairs(n-2)
}

// More efficient iterative version
method ClimbStairsIterative(n: nat) returns (ways: nat)
    ensures ways == climbStairs(n)
{
    if n == 0 {
        return 1;
    } else if n == 1 {
        return 1;
    } else if n == 2 {
        return 2;
    }
    
    var prev2 := 1;
    var prev1 := 1;
    var current := 2;
    var i := 3;
    
    while i <= n
        invariant 3 <= i <= n + 1
        invariant current == climbStairs(i - 1)
        invariant prev1 == climbStairs(i - 2)
        invariant prev2 == climbStairs(i - 3)
    {
        prev2 := prev1;
        prev1 := current;
        current := prev1 + prev2;
        i := i + 1;
    }
    
    return current;
}

method Test() {
    var result := ClimbStairsIterative(5);
    assert result == 8; // There are 8 ways to climb 5 steps
}