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
lemma PalindromeIsPositive(k: int)
    requires k >= 1
    ensures StringToInt(IntToString(k) + ReverseString(IntToString(k))) > 0
{
    var s := IntToString(k);
    var reversed := ReverseString(s);
    var palindrome := s + reversed;
    assert |palindrome| >= 2;
    assert palindrome[0] >= '1'; // First digit of k is at least '1' since k >= 1
}

lemma SumOfPalindromesNonNegative(k: int)
    requires k >= 0
    ensures SumOfPalindromes(k) >= 0
{
    if k == 0 {
        assert SumOfPalindromes(0) == 0;
    } else if k == 1 {
        PalindromeIsPositive(1);
        var s := IntToString(1);
        var reversed := ReverseString(s);
        var palindrome := s + reversed;
        assert StringToInt(palindrome) > 0;
        assert SumOfPalindromes(1) == StringToInt(palindrome);
        assert SumOfPalindromes(1) > 0;
    } else {
        SumOfPalindromesNonNegative(k - 1);
        PalindromeIsPositive(k);
        var s := IntToString(k);
        var reversed := ReverseString(s);
        var palindrome := s + reversed;
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
    
    SumOfPalindromesNonNegative(0);
    
    while i <= k
        invariant 1 <= i <= k + 1
        invariant 0 <= sum < p
        invariant sum == SumOfPalindromes(i - 1) % p
    {
        var s := IntToString(i);
        var reversed := ReverseString(s);
        var palindrome := s + reversed;
        var palindromeInt := StringToInt(palindrome);
        
        SumOfPalindromesNonNegative(i - 1);
        SumOfPalindromesMonotonic(i);
        assert SumOfPalindromes(i) == palindromeInt + SumOfPalindromes(i - 1);
        
        sum := (sum + palindromeInt % p) % p;
        i := i + 1;
    }
    
    assert i == k + 1;
    assert sum == SumOfPalindromes(k) % p;
    result := sum;
}
// </vc-code>

