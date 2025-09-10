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
method ParseTwoNumbers(input: string) returns (x: nat, y: nat)
    requires ValidInput(input)
    ensures x >= 0 && y >= 0
{
    var i := 0;
    x := 0;
    
    // Parse first number
    while i < |input| && input[i] != ' '
        invariant 0 <= i <= |input|
        invariant x >= 0
    {
        if '0' <= input[i] <= '9' {
            x := x * 10 + (input[i] - '0') as nat;
        }
        i := i + 1;
    }
    
    // Skip space
    if i < |input| && input[i] == ' ' {
        i := i + 1;
    }
    
    y := 0;
    // Parse second number
    while i < |input| && input[i] != '\n'
        invariant 0 <= i <= |input|
        invariant y >= 0
    {
        if '0' <= input[i] <= '9' {
            y := y * 10 + (input[i] - '0') as nat;
        }
        i := i + 1;
    }
}

method NatToString(n: nat) returns (s: string)
    ensures |s| > 0
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if n == 0 {
        s := "0";
    } else {
        var temp := n;
        var digits := "";
        while temp > 0
            invariant temp >= 0
            invariant forall i :: 0 <= i < |digits| ==> '0' <= digits[i] <= '9'
            decreases temp
        {
            var digit := (temp % 10) as char + '0';
            digits := [digit] + digits;
            temp := temp / 10;
        }
        s := digits;
        if |s| == 0 {
            s := "0";
        }
    }
}

method ComputeGCD(a: nat, b: nat) returns (g: nat)
    ensures g == gcd(a, b)
{
    if a == 0 {
        g := b;
    } else if b == 0 {
        g := a;
    } else {
        var x := a;
        var y := b;
        while y != 0
            invariant gcd(x, y) == gcd(a, b)
            invariant x >= 0 && y >= 0
            decreases y
        {
            var temp := y;
            y := x % y;
            x := temp;
        }
        g := x;
    }
}

method ComputeF(x: nat, y: nat) returns (result: nat)
    ensures result == f_mathematical(x, y)
{
    if y == 0 {
        result := 0;
    } else {
        result := 0;
        var remaining := y;
        
        while remaining > 0
            invariant 0 <= remaining <= y
            invariant result + f_mathematical(x, remaining) == f_mathematical(x, y)
            decreases remaining
        {
            var g := ComputeGCD(x, remaining);
            result := result + 1;
            if g >= remaining {
                remaining := 0;
            } else {
                remaining := remaining - g;
            }
        }
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
    var x, y := ParseTwoNumbers(input);
    var f_result := ComputeF(x, y);
    var f_str := NatToString(f_result);
    result := f_str + "\n";
}
// </vc-code>

