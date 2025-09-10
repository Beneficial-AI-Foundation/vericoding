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
lemma gcd_positive(a: nat, b: nat)
    ensures gcd(a, b) > 0 || (a == 0 && b == 0)
    decreases a + b
{
    if a != 0 || b != 0 {
        if a == 0 {
            assert b != 0;
        } else if b == 0 {
            assert a != 0;
        } else if a > b {
            gcd_positive(a - b, b);
        } else {
            gcd_positive(a, b - a);
        }
    }
}

lemma gcd_le(a: nat, b: nat)
    requires a > 0 && b > 0
    ensures gcd(a, b) <= a
    ensures gcd(a, b) <= b
    decreases a + b
{
    if a == 0 || b == 0 {
        assert false;
    } else if a > b {
        gcd_le(a - b, b);
    } else if b > a {
        gcd_le(a, b - a);
    } else {
        // a == b
    }
}

lemma gcd_divides(a: nat, b: nat)
    ensures (a != 0 || b != 0) ==> (a % gcd(a, b) == 0 && b % gcd(a, b) == 0)
    decreases a + b
{
    if a != 0 || b != 0 {
        if a == 0 {
            // gcd(0, b) == b, b % b == 0
        } else if b == 0 {
            // gcd(a, 0) == a, a % a == 0
        } else if a > b {
            gcd_divides(a - b, b);
        } else {
            gcd_divides(a, b - a);
        }
    }
}

lemma f_termination(x: nat, y: nat)
    requires y > 0
    ensures y - gcd(x, y) < y
    decreases y
{
    gcd_positive(x, y);
    if x > 0 {
        gcd_le(x, y);
        assert gcd(x, y) <= y;
        assert gcd(x, y) > 0;
        assert y - gcd(x, y) < y;
    } else {
        assert gcd(0, y) == y;
        assert y - y == 0 < y;
    }
}

function intToString(n: nat): string
    ensures |intToString(n)| > 0
    ensures forall i :: 0 <= i < |intToString(n)| ==> '0' <= intToString(n)[i] <= '9'
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else intToString(n / 10) + [('0' as int + n % 10) as char]
}

lemma gcd_nonzero_positive(a: nat, b: nat)
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
{
    gcd_positive(a, b);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    var index := 0;
    var output := "";
    var spaceFound := false;
    var firstNum := 0;
    var secondNum := 0;
    var currentNum := 0;
    
    while index < |input| && !spaceFound
        invariant 0 <= index <= |input|
        invariant currentNum >= 0
        invariant forall i :: 0 <= i < |output| ==> ('0' <= output[i] <= '9' || output[i] == '\n')
        invariant |output| >= 0
    {
        if input[index] == ' ' {
            spaceFound := true;
            firstNum := currentNum;
            currentNum := 0;
        } else if input[index] != '\n' {
            currentNum := currentNum * 10 + (input[index] as int - '0' as int);
        }
        index := index + 1;
    }
    
    while index < |input|
        invariant index <= |input|
        invariant currentNum >= 0
    {
        if input[index] != '\n' {
            currentNum := currentNum * 10 + (input[index] as int - '0' as int);
        }
        index := index + 1;
    }
    
    secondNum := currentNum;
    var count := 0;
    var y := secondNum;
    
    while y > 0
        invariant y >= 0
        invariant count >= 0
        decreases y
    {
        var g: nat;
        if firstNum == 0 && y == 0 {
            g := 0;
        } else {
            gcd_nonzero_positive(firstNum, y);
            g := gcd(firstNum, y);
        }
        count := count + 1;
        y := y - g;
    }
    
    output := output + intToString(count) + "\n";
    result := output;
}
// </vc-code>

