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
function ParseNat(s: string): nat
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 0 then 0
    else
        var last := s[|s|-1];
        var rest := s[0..|s|-1];
        10 * ParseNat(rest) + (last - '0') as nat
}

function NatToString(n: nat): string
    decreases n
    ensures NatToString(n) == "" || (forall i :: 0 <= i < |NatToString(n)| ==> '0' <= NatToString(n)[i] <= '9')
{
    if n == 0 then "0"
    else if n < 10 then [ '0' + n as char ]
    else NatToString(n / 10) + NatToString(n % 10)
}

lemma ValidInputImpliesTokenIsDigits(s: string, start: int, end: int)
    requires ValidInput(s)
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> s[i] != ' ' && s[i] != '\n'
    ensures forall i :: start <= i < end ==> '0' <= s[i] <= '9'
{
    forall i | start <= i < end
        ensures '0' <= s[i] <= '9'
    {
        assert '0' <= s[i] <= '9';
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < |input| && input[i] != ' ' && input[i] != '\n'
        invariant 0 <= i <= |input|
    {
        i := i + 1;
    }
    var token1 := input[0..i];

    var j := i;
    while j < |input| && (input[j] == ' ' || input[j] == '\n')
        invariant i <= j <= |input|
    {
        j := j + 1;
    }

    var k := j;
    while k < |input| && input[k] != ' ' && input[k] != '\n'
        invariant j <= k <= |input|
    {
        k := k + 1;
    }
    var token2 := input[j..k];

    if |token1| == 0 || |token2| == 0 {
        return "0\n";
    }

    ValidInputImpliesTokenIsDigits(input, 0, i);
    ValidInputImpliesTokenIsDigits(input, j, k);

    var x := ParseNat(token1);
    var y := ParseNat(token2);
    var res := f_mathematical(x, y);
    return NatToString(res) + "\n";
}
// </vc-code>

