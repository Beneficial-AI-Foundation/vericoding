// ATOM 
function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}

// IMPL 
method calcF(n: nat) returns (res: nat)  
 ensures res == F(n) 
{
    if n <= 2 {
        res := n;
    } else {
        var dp := new nat[n + 1];
        dp[0] := 0;
        dp[1] := 1;
        dp[2] := 2;
        
        var i := 3;
        while i <= n
            invariant 3 <= i <= n + 1
            invariant forall j :: 0 <= j < i ==> dp[j] == F(j)
        {
            dp[i] := dp[i-1] + dp[i-3];
            i := i + 1;
        }
        
        res := dp[n];
    }
}