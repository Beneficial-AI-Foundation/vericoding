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
lemma lemma_GCDPositive(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
{
}

lemma lemma_LCMProperty(a: int, b: int)
    requires a > 0 && b > 0
    ensures LCM(a, b) > 0
    ensures LCM(a, b) % a == 0 && LCM(a, b) % b == 0
{
}

lemma lemma_StringToIntNonNegative(s: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToInt(s) >= 0
{
}

lemma lemma_MultiplicationCommutative(a: int, b: int)
    ensures a * b == b * a
{
}

lemma lemma_DivisionByGCD(a: int, b: int)
    requires a > 0 && b > 0
    ensures (a * b) % gcd(a, b) == 0
{
}

lemma lemma_ProductOfIntsIsPositive(a: int, b: int)
    requires a > 0 && b > 0
    ensures a * b > 0
{
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
    var spaceIndex := FindSpace(input, 0);
    var firstPart := input[..spaceIndex];
    var secondPart := input[spaceIndex+1..];
    var first := StringToInt(firstPart);
    var second := StringToInt(secondPart);
    var product := first * second;
    var gcd_val := gcd(first, second);
    var lcm_val := product / gcd_val;
    result := IntToString(lcm_val);
}
// </vc-code>

