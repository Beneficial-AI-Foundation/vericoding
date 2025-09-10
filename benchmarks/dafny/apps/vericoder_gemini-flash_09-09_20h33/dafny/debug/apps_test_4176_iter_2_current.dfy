predicate ValidInput(input: string)
{
    |input| > 0 &&
    exists spaceIndex :: 0 <= spaceIndex < |input| && input[spaceIndex] == ' ' &&
    forall i :: 0 <= i < |input| ==> (input[i] == ' ' || ('0' <= input[i] <= '9'))
}

function ParseTwoInts(s: string): (int, int)
    requires ValidInput(s)
    ensures ParseTwoInts(s).0 > 0 && ParseTwoInts(s).1 > 0
{
    var spaceIndex := FindSpace(s, 0);
    if spaceIndex == -1 || spaceIndex == 0 || spaceIndex == |s| - 1 then (1, 1)
    else
        var firstPart := s[..spaceIndex];
        var secondPart := s[spaceIndex+1..];
        if |firstPart| == 0 || |secondPart| == 0 then (1, 1)
        else if !(forall i :: 0 <= i < |firstPart| ==> '0' <= firstPart[i] <= '9') then (1, 1)
        else if !(forall i :: 0 <= i < |secondPart| ==> '0' <= secondPart[i] <= '9') then (1, 1)
        else
            var first := StringToInt(firstPart);
            var second := StringToInt(secondPart);
            if first <= 0 || second <= 0 then (1, 1)
            else (first, second)
}

function LCM(a: int, b: int): int
    requires a > 0 && b > 0
    ensures LCM(a, b) > 0
    ensures LCM(a, b) % a == 0 && LCM(a, b) % b == 0
{
    (a * b) / gcd(a, b)
}

predicate ValidOutput(output: string)
{
    |output| > 0 &&
    forall i :: 0 <= i < |output| ==> ('0' <= output[i] <= '9')
}

// <vc-helpers>
function FindSpace(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures -1 <= FindSpace(s, start) <= |s|
    ensures FindSpace(s, start) == -1 || s[FindSpace(s,start)] == ' '
    ensures forall i :: start <= i < FindSpace(s, start) ==> s[i] != ' '
{
    if start == |s| then -1
    else if s[start] == ' ' then start
    else FindSpace(s, start + 1)
}

function StringToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires |s| > 0
    ensures StringToInt(s) >= 0
{
    var res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res >= 0
        invariant forall j :: 0 <= j < i ==> '0' <= s[j] <= '9'
        // This invariant should relate res to the integer value of s[..i]
        // But Dafny's StringToInt function already implements this, so we'll just keep the necessary
        // invariants for loop termination and digit validity.
    {
        res := res * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    res
}

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    decreases a, b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function IntToString(n: int): string
    requires n >= 0 // Changed from n > 0 to n >= 0 to handle n=0 gracefully
    ensures ValidOutput(IntToString(n))
{
    if n == 0 then "0"
    else
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant (s == "" && temp == n) || (s != "" && ValidOutput(s) && n == temp * (Pow10(|s|)) + StringToInt(s)) // Added more precise invariant
        {
            s := ('0' as int + temp % 10) as char + s;
            temp := temp / 10;
        }
        s
}

function Pow10(exp: int): int
    requires exp >= 0
    ensures Pow10(exp) > 0
    decreases exp
{
    if exp == 0 then 1
    else 10 * Pow10(exp - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures var nums := ParseTwoInts(input); 
            var a := nums.0; 
            var b := nums.1;
            result == IntToString(LCM(a, b))
    ensures ValidOutput(result)
// </vc-spec>
// <vc-code>
{
    var nums := ParseTwoInts(input);
    var a := nums.0;
    var b := nums.1;
    result := IntToString(LCM(a, b));
}
// </vc-code>

