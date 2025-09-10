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
function gcd(a: nat, b: nat): nat
    ensures gcd(a, b) > 0 || (a == 0 && b == 0)
    ensures a > 0 ==> gcd(a, b) <= a
    ensures b > 0 ==> gcd(a, b) <= b
    ensures (a != 0 || b != 0) ==> (a % gcd(a, b) == 0 && b % gcd(a, b) == 0)
    ensures gcd(a, 0) == a
    ensures gcd(0, b) == b
    decreases if a < b then b else a
{
    if a == 0 then b
    else if b == 0 then a  
    else if a == b then a
    else if a > b then gcd(a % b, b)
    else gcd(a, b % a)
}

function parseNat(s: string, start: int, end: int): nat
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
    decreases end - start
{
    if start >= end then 0
    else if start + 1 == end then (s[start] as int) - ('0' as int)
    else parseNat(s, start, end - 1) * 10 + ((s[end - 1] as int) - ('0' as int))
}

function natToString(n: nat): string
    ensures |natToString(n)| > 0
    ensures forall i :: 0 <= i < |natToString(n)| ==> '0' <= natToString(n)[i] <= '9'
    decreases n
{
    if n < 10 then [('0' as int + n) as char]
    else natToString(n / 10) + [('0' as int + n % 10) as char]
}

lemma parseNatCorrect(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
    ensures parseNat(s, start, end) >= 0
{}

lemma natToStringCorrect(n: nat)
    ensures |natToString(n)| > 0
    ensures forall i :: 0 <= i < |natToString(n)| ==> '0' <= natToString(n)[i] <= '9'
{}

lemma ValidInputDigitsProperty(input: string, start: int, end: int)
    requires ValidInput(input)
    requires 0 <= start <= end <= |input|
    requires forall i :: start <= i < end ==> input[i] != ' ' && input[i] != '\n'
    ensures forall i :: start <= i < end ==> '0' <= input[i] <= '9'
{
    forall i | start <= i < end
        ensures '0' <= input[i] <= '9'
    {
        assert 0 <= i < |input|;
        assert input[i] != ' ' && input[i] != '\n';
        assert '0' <= input[i] <= '9' || input[i] == ' ' || input[i] == '\n';
    }
}

lemma EstablishDigitsProperty(input: string, start: int, end: int)
    requires ValidInput(input)
    requires 0 <= start <= end <= |input|
    requires forall i :: start <= i < end ==> input[i] != ' ' && input[i] != '\n'
    ensures forall i :: start <= i < end ==> '0' <= input[i] <= '9'
{
    forall i | start <= i < end
        ensures '0' <= input[i] <= '9'
    {
        assert 0 <= i < |input|;
        assert input[i] != ' ' && input[i] != '\n';
        assert '0' <= input[i] <= '9' || input[i] == ' ' || input[i] == '\n';
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
    var spaceIndex := 0;
    while spaceIndex < |input| && input[spaceIndex] != ' '
        invariant 0 <= spaceIndex <= |input|
        invariant forall j :: 0 <= j < spaceIndex ==> input[j] != ' '
    {
        spaceIndex := spaceIndex + 1;
    }
    
    var firstNumEnd := spaceIndex;
    while firstNumEnd > 0 && input[firstNumEnd - 1] == ' '
        invariant 0 <= firstNumEnd <= spaceIndex
    {
        firstNumEnd := firstNumEnd - 1;
    }
    
    var secondNumStart := spaceIndex;
    while secondNumStart < |input| && (input[secondNumStart] == ' ')
        invariant spaceIndex <= secondNumStart <= |input|
    {
        secondNumStart := secondNumStart + 1;
    }
    
    var secondNumEnd := |input|;
    while secondNumEnd > secondNumStart && (input[secondNumEnd - 1] == ' ' || input[secondNumEnd - 1] == '\n')
        invariant secondNumStart <= secondNumEnd <= |input|
        invariant forall j :: secondNumEnd <= j < |input| ==> (input[j] == ' ' || input[j] == '\n')
    {
        secondNumEnd := secondNumEnd - 1;
    }
    
    ghost var firstNonSpaceFound := false;
    var i := 0;
    while i < firstNumEnd
        invariant 0 <= i <= firstNumEnd
        invariant forall j :: 0 <= j < i ==> input[j] != ' ' && input[j] != '\n'
    {
        assert 0 <= i < |input|;
        assert '0' <= input[i] <= '9' || input[i] == ' ' || input[i] == '\n';
        assert i < spaceIndex;
        assert input[i] != ' ';
        if input[i] == '\n' {
            assert false;
        }
        i := i + 1;
    }
    
    var j := secondNumStart;
    while j < secondNumEnd
        invariant secondNumStart <= j <= secondNumEnd
        invariant forall k :: secondNumStart <= k < j ==> input[k] != ' ' && input[k] != '\n'
    {
        assert secondNumStart <= j < |input|;
        assert '0' <= input[j] <= '9' || input[j] == ' ' || input[j] == '\n';
        assert input[j] != ' ';
        if input[j] == '\n' {
            assert false;
        }
        j := j + 1;
    }
    
    EstablishDigitsProperty(input, 0, firstNumEnd);
    EstablishDigitsProperty(input, secondNumStart, secondNumEnd);
    
    var x := parseNat(input, 0, firstNumEnd);
    var y := parseNat(input, secondNumStart, secondNumEnd);
    
    var mathResult := f_mathematical(x, y);
    var resultStr := natToString(mathResult);
    
    result := resultStr + ['\n'];
}
// </vc-code>

