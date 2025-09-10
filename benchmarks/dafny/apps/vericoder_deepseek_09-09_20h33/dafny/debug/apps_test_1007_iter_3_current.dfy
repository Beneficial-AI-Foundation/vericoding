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
lemma SumOfPalindromesModLemma(k: int, p: int)
    requires k >= 0
    requires p >= 1
    ensures (SumOfPalindromes(k) % p) == if k == 0 then 0 else (SumOfPalindromes(k) % p)
    decreases k
{
    if k > 0 {
        SumOfPalindromesModLemma(k - 1, p);
    }
}

lemma ReverseStringPreservesDigits(s: string)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures forall i :: 0 <= i < |ReverseString(s)| ==> '0' <= ReverseString(s)[i] <= '9'
{
}

lemma IntToStringDigits(n: int)
    requires n >= 0
    ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
{
}

lemma StringToIntValid(s: string)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToInt(s) >= 0
{
}

lemma SumOfPalindromesModLemma2(k: int, p: int)
    requires k >= 0
    requires p >= 1
    ensures SumOfPalindromes(k) % p == (if k == 0 then 0 else (StringToInt(IntToString(k) + ReverseString(IntToString(k))) + SumOfPalindromes(k - 1)) % p) % p
    decreases k
{
    if k > 0 {
        var s := IntToString(k);
        IntToStringDigits(k);
        var reversed := ReverseString(s);
        ReverseStringPreservesDigits(s);
        var palindrome := s + reversed;
        var num := StringToInt(palindrome);
        StringToIntValid(palindrome);
        SumOfPalindromesModLemma2(k - 1, p);
        
        // Use the property that (a + b) % p == (a % p + b % p) % p
        assert num % p == StringToInt(palindrome) % p;
        assert SumOfPalindromes(k) == num + SumOfPalindromes(k - 1);
        assert (SumOfPalindromes(k)) % p == (num + SumOfPalindromes(k - 1)) % p;
        assert (num + SumOfPalindromes(k - 1)) % p == (num % p + SumOfPalindromes(k - 1) % p) % p;
        assert (num % p + SumOfPalindromes(k - 1) % p) % p == (num % p + (SumOfPalindromes(k - 1) % p) % p) % p;
    }
}

lemma ModAdditionLemma(a: int, b: int, p: int)
    requires p >= 1
    ensures (a + b) % p == (a % p + b % p) % p
{
    calc {
        (a + b) % p;
        == { assert (a + b) % p == ((a % p) + (b % p)) % p; }
        (a % p + b % p) % p;
    }
}

lemma ModAssociativeLemma(a: int, b: int, p: int)
    requires p >= 1
    ensures ((a % p) + (b % p)) % p == (a + (b % p)) % p
{
}

lemma ModTransitiveLemma(a: int, p: int)
    requires p >= 1
    ensures (a % p) % p == a % p
{
}
// </vc-helpers>
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
        invariant sum == SumOfPalindromes(i - 1) % p
        decreases k - i
    {
        var s := IntToString(i);
        IntToStringDigits(i);
        var reversed := ReverseString(s);
        ReverseStringPreservesDigits(s);
        var palindrome := s + reversed;
        var num := StringToInt(palindrome);
        StringToIntValid(palindrome);
        
        SumOfPalindromesModLemma2(i, p);
        assert SumOfPalindromes(i) % p == (num + SumOfPalindromes(i - 1)) % p;
        ModAdditionLemma(SumOfPalindromes(i - 1), num, p);
        assert (SumOfPalindromes(i - 1) + num) % p == (SumOfPalindromes(i - 1) % p + num % p) % p;
        
        sum := (sum + (num % p)) % p;
        assert sum == (SumOfPalindromes(i - 1) % p + num % p) % p;
        assert sum == SumOfPalindromes(i) % p;
        
        i := i + 1;
    }
    result := sum;
}
// </vc-code>

