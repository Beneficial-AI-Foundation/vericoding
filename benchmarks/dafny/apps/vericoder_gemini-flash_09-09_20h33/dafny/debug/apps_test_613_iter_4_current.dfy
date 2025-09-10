predicate ValidInput(t: int, a: int, b: int)
{
    t > 0 && a > 0 && b > 0
}

predicate ValidOutput(res: string)
{
    res == "0" || res == "1" || res == "2" || res == "inf"
}

predicate InfiniteCase(t: int, a: int, b: int)
{
    a == t && a == b && a == 1
}

predicate TwoSolutionsCase(t: int, a: int, b: int)
{
    a == t && a == b && a != 1
}

predicate ZeroSolutionsCase(t: int, a: int, b: int)
{
    (t == 2 && a == 3 && b > 10000) ||
    (a == t && a != b) ||
    (a != t && (a - b) % (t - a) == 0) ||
    (a != t && (a - b) % (t - a) != 0 && t == b)
}

predicate OneSolutionCase(t: int, a: int, b: int)
{
    a != t && (a - b) % (t - a) != 0 && t != b
}

// <vc-helpers>
function Modulo(x: int, y: int): int
    requires y != 0
    ensures 0 <= Modulo(x, y) < if y < 0 then -y else y
{
    var r := x % y;
    if r < 0 then r + y else r
}
// </vc-helpers>

// <vc-spec>
method solve(t: int, a: int, b: int) returns (res: string)
    requires ValidInput(t, a, b)
    requires t != a || a == t
    ensures ValidOutput(res)
    ensures InfiniteCase(t, a, b) ==> res == "inf"
    ensures TwoSolutionsCase(t, a, b) ==> res == "2"
    ensures ZeroSolutionsCase(t, a, b) ==> res == "0"
    ensures OneSolutionCase(t, a, b) ==> res == "1"
// </vc-spec>
// <vc-code>
{
    if t == a {
        if a == b {
            if a == 1 {
                res := "inf";
            } else {
                res := "2";
            }
        } else {
            // t == a and a != b
            res := "0";
        }
    } else {
        // t != a
        if (a - b) % (t - a) != 0 {
            if t == b {
                res := "0";
            } else {
                res := "1";
            }
        } else {
            // (a - b) % (t - a) == 0
            if t == b {
                 res := "0"; 
            } else {
                res := "1";
            }
        }
    }
}
// </vc-code>

