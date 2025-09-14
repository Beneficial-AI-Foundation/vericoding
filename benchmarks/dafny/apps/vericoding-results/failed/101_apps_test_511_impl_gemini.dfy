predicate ValidInput(input: string)
{
    |input| > 0 &&
    (exists i :: 0 <= i < |input| && input[i] == ' ') &&
    (forall j :: 0 <= j < |input| ==> ('0' <= input[j] <= '9' || input[j] == ' ' || input[j] == '\n'))
}

function gcd(a: nat, b: nat): nat
    ensures gcd(a, b) > 0 || (a == 0 && b == 0)
    ensures a > 0 ==> gcd(a, b) <= a
    ensures b > 0 ==> gcd(a, b) <= b
    ensures (a != 0 || b != 0) ==> (a % gcd(a, b) == 0 && b % gcd(a, b) == 0)
    ensures gcd(a, 0) == a
    ensures gcd(0, b) == b
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a  
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function f_mathematical(x: nat, y: nat): nat
    ensures y == 0 ==> f_mathematical(x, y) == 0
    ensures y > 0 ==> f_mathematical(x, y) > 0
    ensures y > 0 ==> f_mathematical(x, y) <= y
    ensures y > 0 ==> f_mathematical(x, y) == 1 + f_mathematical(x, y - gcd(x, y))
    decreases y
{
    if y == 0 then 0
    else 
        var g := gcd(x, y);
        if g >= y then 1
        else 1 + f_mathematical(x, y - g)
}

predicate ValidOutput(result: string)
{
    |result| > 0 &&
    forall i :: 0 <= i < |result| ==> ('0' <= result[i] <= '9' || result[i] == '\n') &&
    result[|result|-1] == '\n'
}

// <vc-helpers>
function NatToString(n: nat): string
    ensures |NatToString(n)| >= 1
    ensures n > 0 ==> NatToString(n)[0] != '0'
    ensures forall i :: 0 <= i < |NatToString(n)| ==> '0' <= NatToString(n)[i] <= '9'
    decreases n
{
    if n < 10 then
        [char(n + '0')]
    else
        NatToString(n / 10) + [char((n % 10) + '0')]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    var res := "";
    var i := 0;
    var numbers: seq<nat> := [];
    
    while i < |input|
        invariant 0 <= i <= |input|
    {
        while i < |input| && (input[i] == ' ' || input[i] == '\n')
        {
            i := i + 1;
        }

        if i < |input| {
            assert '0' <= input[i] <= '9';
            var current_num: nat := 0;
            var j := i;
            while j < |input| && '0' <= input[j] <= '9'
            {
                var digit := input[j] - '0';
                current_num := current_
// </vc-code>

