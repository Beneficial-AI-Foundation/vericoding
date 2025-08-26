predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

// <vc-helpers>
function SumOfDigits(s: string): int
{
    if |s| == 0 then 0
    else (if IsDigit(s[0]) then (s[0] as int - 48) else 0) + SumOfDigits(s[1..])
}
// </vc-helpers>

// <vc-spec>
method CountSubstringsWithSumOfDigitsEqualToLength(s: string) returns (count: int)
    ensures count >= 0
// </vc-spec>
// <vc-code>
{
    count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count >= 0
    {
        var j := i;
        while j < |s|
            invariant i <= j <= |s|
            invariant count >= 0
        {
            var substring := s[i..j+1];
            var digitSum := SumOfDigits(substring);
            if digitSum == |substring| {
                count := count + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>