// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed PowerIncreases lemma calculation step */
lemma PowerIncreases(x: nat, y: nat)
    requires x > 1
    ensures power(x, y) < power(x, y + 1)
{
    // power(x, y + 1) = x * power(x, y) > power(x, y) when x > 1
    calc {
        power(x, y + 1);
        ==
        x * power(x, y);
        >
        power(x, y);
    }
}

lemma PowerMonotonic(x: nat, y1: nat, y2: nat)
    requires x > 1
    requires y1 < y2
    ensures power(x, y1) < power(x, y2)
    decreases y2 - y1
{
    if y1 + 1 == y2 {
        PowerIncreases(x, y1);
    } else {
        PowerIncreases(x, y1);
        PowerMonotonic(x, y1 + 1, y2);
    }
}

lemma PowerOne(y: nat)
    ensures power(1, y) == 1
{
    if y == 0 {
        // Base case
    } else {
        PowerOne(y - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified logic to ensure postcondition is met */
    if n <= 0 {
        ans := n == 1;
        if ans {
            assert power(x, 0) == 1;
        }
        return;
    }
    
    if x == 1 {
        ans := n == 1;
        if ans {
            assert forall z :: power(1, z) == 1 by { 
                forall z { PowerOne(z); }
            }
        } else {
            assert n != 1;
            assert forall z :: power(1, z) == 1 by { 
                forall z { PowerOne(z); }
            }
            assert forall z :: n != power(1, z);
        }
        return;
    }
    
    var p := 1;
    var y := 0;
    
    while p < n
        invariant p == power(x, y)
        invariant forall j :: 0 <= j < y ==> power(x, j) < n
    {
        p := p * x;
        y := y + 1;
    }
    
    ans := p == n;
    if ans {
        assert n == power(x, y);
    } else {
        assert p > n;
        assert power(x, y) > n;
        assert forall j :: 0 <= j < y ==> power(x, j) < n;
        if x > 1 {
            assert forall j :: j > y ==> power(x, j) > power(x, y) by {
                forall j | j > y { PowerMonotonic(x, y, j); }
            }
            assert forall j :: j > y ==> power(x, j) > n;
        }
        assert !(exists j :: n == power(x, j));
    }
}
// </vc-code>
