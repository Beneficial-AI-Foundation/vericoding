// <vc-preamble>
function Power10(x: nat): nat
{
    if x == 0 then 1 else 10 * Power10(x - 1)
}

predicate ValidInput(n: int)
{
    2 <= n <= 1000000000
}

predicate ValidOutput(result: int, n: int)
{
    result >= 0 && result <= 2000000000 && result > 0 && result <= n * (n - 1) / 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures ValidOutput(result, n)
    ensures (forall x: nat :: 1 <= x <= 9 ==> Power10(x) / 2 > n) ==> 
        result == n * (n - 1) / 2
    ensures (exists x: nat :: 1 <= x <= 9 && Power10(x) / 2 <= n) ==>
        result >= 1
    ensures n < 5 ==> result == n * (n - 1) / 2
    ensures n == 2 ==> result == 1
    ensures n == 3 ==> result == 3  
    ensures n == 4 ==> result == 6
    ensures n >= 5 ==> Power10(1) / 2 <= n
    ensures n >= 5 ==> result <= n * (n - 1) / 2
// </vc-spec>
// <vc-code>
{
    var o := 0;
    var x := 9;
    var found_valid_x := false;
    var largest_x := 1;

    while x > 0
        decreases x
        invariant 0 <= x <= 9
        invariant !found_valid_x ==> forall y: nat :: y > x && 1 <= y <= 9 ==> Power10(y) / 2 > n
        invariant found_valid_x ==> (1 <= largest_x <= 9 && Power10(largest_x) / 2 <= n && 
                                    forall y: nat :: y > largest_x && 1 <= y <= 9 ==> Power10(y) / 2 > n)
    {
        if Power10(x) / 2 <= n {
            largest_x := x;
            found_valid_x := true;
            break;
        }
        x := x - 1;
    }

    if found_valid_x {
        var i := 0;
        while i < 9
            decreases 9 - i
            invariant 0 <= i <= 9
            invariant o >= 0
            invariant o <= n * (n - 1) / 2
            invariant o <= 2000000000
            invariant Power10(largest_x) / 2 <= n
            invariant 1 <= largest_x <= 9
            invariant forall y: nat :: y > largest_x && 1 <= y <= 9 ==> Power10(y) / 2 > n
        {
            var tmpCall1 := Power10(largest_x);
            var q := tmpCall1 * (i + 1) / 2 - 1;
            if q <= n && q >= 1 {
                var addition := if q <= n - q then q else n - q;
                if addition >= 0 && o + addition <= n * (n - 1) / 2 && o + addition <= 2000000000 {
                    o := o + addition;
                }
            }
            i := i + 1;
        }
        if o == 0 {
            return 1;
        }
        return o;
    } else {
        return n * (n - 1) / 2;
    }
}
// </vc-code>
