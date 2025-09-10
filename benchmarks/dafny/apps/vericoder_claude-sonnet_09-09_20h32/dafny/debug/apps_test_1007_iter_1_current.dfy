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
        assert StringToInt("11") == 11;
    } else {
        // Inductive case
        SumOfPalindromesNonNegative(k - 1);
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

