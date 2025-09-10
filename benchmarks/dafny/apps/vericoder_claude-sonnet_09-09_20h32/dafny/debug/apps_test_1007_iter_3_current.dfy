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
lemma SumOfPalindromesNonNegative(k: int)
    requires k >= 0
    ensures SumOfPalindromes(k) >= 0
{
    if k == 0 {
        // Base case: SumOfPalindromes(0) == 0
    } else if k == 1 {
        // SumOfPalindromes(1) is positive since it's a palindrome of "1"
        assert IntToString(1) == "1";
        assert ReverseString("1") == "1";
        var palindrome := "1" + "1";
        assert palindrome == "11";
        assert StringToInt("11") == StringToInt("1") * 10 + 1 == 1 * 10 + 1 == 11;
        assert SumOfPalindromes(1) == 11;
    } else {
        // Inductive case
        SumOfPalindromesNonNegative(k - 1);
        // Need to prove that the current palindrome is positive
        var s := IntToString(k);
        var reversed := ReverseString(s);
        var palindrome := s + reversed;
        IntToStringPositive(k);
        PalindromeIsPositive(s, reversed, palindrome);
    }
}

lemma IntToStringPositive(n: int)
    requires n >= 1
    ensures var s := IntToString(n); |s| >= 1 && s[0] >= '1'
{
    var s := IntToString(n);
    if n < 10 {
        assert s == [('0' as int + n) as char];
        assert |s| == 1;
        assert s[0] == ('0' as int + n) as char;
        assert n >= 1;
        assert s[0] >= ('0' as int + 1) as char == '1';
    } else {
        IntToStringPositive(n / 10);
        assert n / 10 >= 1;
        var prefix := IntToString(n / 10);
        assert |prefix| >= 1 && prefix[0] >= '1';
        assert s == prefix + [('0' as int + (n % 10)) as char];
        assert s[0] == prefix[0];
        assert s[0] >= '1';
    }
}

lemma PalindromeIsPositive(s: string, reversed: string, palindrome: string)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires forall i :: 0 <= i < |reversed| ==> '0' <= reversed[i] <= '9'
    requires palindrome == s + reversed
    requires s[0] >= '1'
    ensures StringToInt(palindrome) > 0
{
    assert |palindrome| == |s| + |reversed|;
    assert |palindrome| >= 2;
    assert palindrome[0] == s[0];
    assert s[0] >= '1';
    // Since palindrome starts with a digit >= '1', StringToInt(palindrome) > 0
    StringToIntPositive(palindrome);
}

lemma StringToIntPositive(s: string)
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires s[0] >= '1'
    ensures StringToInt(s) > 0
{
    if |s| == 1 {
        assert StringToInt(s) == (s[0] as int) - ('0' as int);
        assert s[0] >= '1';
        assert StringToInt(s) >= ('1' as int) - ('0' as int) == 1;
    } else {
        var prefix := s[0..|s|-1];
        assert prefix[0] == s[0] >= '1';
        StringToIntPositive(prefix);
        assert StringToInt(prefix) > 0;
        assert StringToInt(s) == StringToInt(prefix) * 10 + ((s[|s|-1] as int) - ('0' as int));
        assert StringToInt(s) >= StringToInt(prefix) * 10 >= 1 * 10 == 10;
    }
}

lemma ModuloProperties(a: int, p: int)
    requires p > 0
    ensures 0 <= a % p < p
{
    // Dafny's built-in modulo properties
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
    SumOfPalindromesNonNegative(k);
    var sum := SumOfPalindromes(k);
    ModuloProperties(sum, p);
    result := sum % p;
}
// </vc-code>

