//ATOM
function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}

//IMPL calcF
method calcF(n: nat) returns (res: nat) 
 ensures res == F(n) 
{
    if n <= 2 {
        res := n;
    } else {
        /* code modified by LLM (iteration 1): Fixed variable initialization to match F(0), F(1), F(2) and corrected loop invariants */
        var a, b, c := 0, 1, 2;  // F(0), F(1), F(2)
        var i := 3;
        while i <= n
            invariant 3 <= i <= n + 1
            invariant a == F(i-3)
            invariant b == F(i-2)
            invariant c == F(i-1)
        {
            /* code modified by LLM (iteration 1): Added assertion to help verification and updated variable assignments */
            assert c == F(i-1) && a == F(i-3);
            var next := c + a;
            assert next == F(i-1) + F(i-3) == F(i);
            a, b, c := b, c, next;
            i := i + 1;
        }
        res := c;
    }
}