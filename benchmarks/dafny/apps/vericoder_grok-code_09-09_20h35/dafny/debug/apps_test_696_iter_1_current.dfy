predicate ValidInput(p: int) {
    2 <= p < 2000
}

function CountPrimitiveRoots(p: int): int
    requires ValidInput(p)
{
    if p == 2 then 1
    else |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|
}

// <vc-helpers>
function gcd(a: int, b: int): int
    requires a >= 0 && b >= 0
{
    if b == 0 then a
    else gcd(b, a % b)
}
// </vc-helpers>

// <vc-spec>
method solve(p: int) returns (result: int)
    requires ValidInput(p)
    ensures result >= 0
    ensures result == CountPrimitiveRoots(p)
// </vc-spec>
// <vc-code>
{
    var count := 0;
    for i := 1 to p - 2 {
        if gcd(i, p - 1) == 1 {
            count := count + 1;
        }
    }
    if p == 2 {
        return 1;
    } else {
        return count;
    }
}
// </vc-code>

