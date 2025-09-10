function IntToString(n: int): string
    requires n >= 0
    ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + [('0' as int + (n % 10)) as char]
}

function ReverseString(s: string): string
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures forall i :: 0 <= i < |ReverseString(s)| ==> '0' <= ReverseString(s)[i] <= '9'
{
    if |s| == 0 then ""
    else ReverseString(s[1..]) + [s[0]]
}

function StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then (s[0] as int) - ('0' as int)
    else StringToInt(s[0..|s|-1]) * 10 + ((s[|s|-1] as int) - ('0' as int))
}

function SumOfPalindromes(k: int): int
    requires k >= 0
{
    if k == 0 then 0
    else if k == 1 then
        var s := IntToString(1);
        var reversed := ReverseString(s);
        var palindrome := s + reversed;
        StringToInt(palindrome)
    else
        var s := IntToString(k);
        var reversed := ReverseString(s);
        var palindrome := s + reversed;
        StringToInt(palindrome) + SumOfPalindromes(k - 1)
}

predicate ValidInput(k: int, p: int)
{
    k >= 1 && p >= 1
}

// <vc-helpers>
lemma IntToStringFirstDigit(n: int)
    requires n >= 1
    ensures |IntToString(n)| >= 1
    ensures IntToString(n)[0] >= '1'
    ensures IntToString(n)[0] <= '9'
{
    if n < 10 {
        assert IntToString(n) == [('0' as int + n) as char];
        assert IntToString(n)[0] == ('0' as int + n) as char;
        assert n >= 1 && n <= 9;
        assert IntToString(n)[0] >= '1';
    } else {
        IntToStringFirstDigit(n / 10);
        var prefix := IntToString(n / 10);
        var suffix := [('0' as int + (n % 10)) as char];
        assert IntToString(n) == prefix + suffix;
        assert IntToString(n)[0] == prefix[0];
    }
}

lemma PalindromeStringValid(k: int)
    requires k >= 1
    ensures |IntToString(k) + ReverseString(IntToString(k))| > 0
    ensures forall i :: 0 <= i < |IntToString(k) + ReverseString(IntToString(k))| ==> 
            '0' <= (IntToString(k) + ReverseString(IntToString(k)))[i] <= '9'
{
    var s := IntToString(k);
    var reversed := ReverseString(s);
    var palindrome := s + reversed;
    
    assert forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9';
    assert forall i :: 0 <= i < |reversed| ==> '0' <= reversed[i] <= '9';
    
    assert |palindrome| == |s| + |reversed|;
    assert |s| >= 1;
    assert |palindrome| >= 1;
    
    forall i | 0 <= i < |palindrome|
        ensures '0' <= palindrome[i] <= '9'
    {
        if i < |s| {
            assert palindrome[i] == s[i];
        } else {
            assert palindrome[i] == reversed[i - |s|];
        }
    }
}

lemma PalindromeIsPositive(k: int)
    requires k >= 1
    ensures StringToInt(IntToString(k) + ReverseString(IntToString(k))) > 0
{
    var s := IntToString(k);
    var reversed := ReverseString(s);
    var palindrome := s + reversed;
    
    PalindromeStringValid(k);
    IntToStringFirstDigit(k);
    
    assert |s| >= 1;
    assert s[0] >= '1';
    assert |palindrome| >= 2;
    assert palindrome[0] == s[0];
    assert palindrome[0] >= '1';
    
    assert StringToInt(palindrome) > 0;
}

lemma SumOfPalindromesNonNegative(k: int)
    requires k >= 0
    ensures SumOfPalindromes(k) >= 0
    decreases k
{
    if k == 0 {
        assert SumOfPalindromes(0) == 0;
    } else if k == 1 {
        PalindromeIsPositive(1);
        var s := IntToString(1);
        var reversed := ReverseString(s);
        var palindrome := s + reversed;
        PalindromeStringValid(1);
        assert StringToInt(palindrome) > 0;
        assert SumOfPalindromes(1) == StringToInt(palindrome);
        assert SumOfPalindromes(1) > 0;
    } else {
        SumOfPalindromesNonNegative(k - 1);
        PalindromeIsPositive(k);
        var s := IntToString(k);
        var reversed := ReverseString(s);
        var palindrome := s + reversed;
        PalindromeStringValid(k);
        assert StringToInt(palindrome) > 0;
        assert SumOfPalindromes(k) == StringToInt(palindrome) + SumOfPalindromes(k - 1);
        assert SumOfPalindromes(k) >= SumOfPalindromes(k - 1);
    }
}

lemma SumOfPalindromesMonotonic(k: int)
    requires k >= 1
    ensures SumOfPalindromes(k) >= SumOfPalindromes(k - 1)
{
    PalindromeIsPositive(k);
    var s := IntToString(k);
    var reversed := ReverseString(s);
    var palindrome := s + reversed;
    PalindromeStringValid(k);
    assert StringToInt(palindrome) > 0;
    assert SumOfPalindromes(k) == StringToInt(palindrome) + SumOfPalindromes(k - 1);
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, p: int) returns (result: int)
    requires ValidInput(k, p)
    ensures 0 <= result < p
    ensures result == (SumOfPalindromes(k) % p)
// </vc-spec>
// <vc-code>
{
    var sum := 0;
    var i := 1;
    
    while i <= k
        invariant 1 <= i <= k + 1
        invariant 0 <= sum < p
        invariant sum == SumOfPalindromes(i - 1) % p
    {
        var s := IntToString(i);
        var reversed := ReverseString(s);
        var palindrome := s + reversed;
        
        PalindromeStringValid(i);
        var palindromeInt := StringToInt(palindrome);
        
        PalindromeIsPositive(i);
        
        sum := (sum + palindromeInt % p) % p;
        i := i + 1;
    }
    
    result := sum;
}
// </vc-code>

