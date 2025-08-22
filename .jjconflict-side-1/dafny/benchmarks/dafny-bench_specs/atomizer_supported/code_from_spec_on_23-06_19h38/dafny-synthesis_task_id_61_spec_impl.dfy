// ATOM 
predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

// IMPL CountSubstringsWithSumOfDigitsEqualToLength
method CountSubstringsWithSumOfDigitsEqualToLength(s: string) returns (count: int)
    ensures count >= 0
{
    count := 0;
    var n := |s|;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant count >= 0
    {
        var j := i;
        var digitSum := 0;
        
        while j < n
            invariant i <= j <= n
            invariant count >= 0
            invariant digitSum >= 0
        {
            if IsDigit(s[j]) {
                digitSum := digitSum + (s[j] as int - 48);
            }
            
            var substringLength := j - i + 1;
            if digitSum == substringLength {
                count := count + 1;
            }
            
            j := j + 1;
        }
        
        i := i + 1;
    }
}