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
lemma ModuloProperty(x: int, y: int, p: int)
    requires p > 0
    ensures (x + y) % p == (x % p + y % p) % p
{
    calc {
        (x + y) % p;
        == ((x % p + p * (x / p)) + (y % p + p * (y / p))) % p;
        == ((x % p + y % p) + p * (x / p + y / p)) % p;
        == (x % p + y % p) % p;
    }
}

lemma SumOfPalindromesModuloLemmaHelper(k: int, p: int)
    requires k >= 0
    requires p > 0
    ensures SumOfPalindromes(k) % p == (StringToInt(IntToString(k) + ReverseString(IntToString(k))) % p + SumOfPalindromes(k-1) % p) % p
{
    if k == 0 {
        calc {
            SumOfPalindromes(0) % p;
            0 % p;
            0;
            (0 + 0) % p;
            (StringToInt(IntToString(0) + ReverseString(IntToString(0))) % p + SumOfPalindromes(-1) % p) % p;
        }
    } else {
        calc {
            SumOfPalindromes(k) % p;
            (StringToInt(IntToString(k) + ReverseString(IntToString(k))) + SumOfPalindromes(k-1)) % p;
            (StringToInt(IntToString(k) + ReverseString(IntToString(k))) % p + SumOfPalindromes(k-1) % p) % p
            { ModuloProperty(StringToInt(IntToString(k) + ReverseString(IntToString(k))), SumOfPalindromes(k-1), p); };
        }
    }
}

lemma StringToIntBounds(s: string) returns (n: int)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires |s| > 0
    ensures n == StringToInt(s)
    ensures n >= 0
    decreases |s|
{
    if |s| == 1 {
        n := (s[0] as int) - ('0' as int);
    } else {
        var m := StringToIntBounds(s[0..|s|-1]);
        n := m * 10 + ((s[|s|-1] as int) - ('0' as int));
        assert n >= 0;
    }
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
    {
        var s := IntToString(i);
        var reversed := ReverseString(s);
        var palindrome := s + reversed;
        var palindromeInt := StringToInt(palindrome);
        
        var prevSum := sum;
        sum := (sum + palindromeInt) % p;
        
        calc {
            sum;
            == (prevSum + palindromeInt) % p;
            == (SumOfPalindromes(i - 1) % p + palindromeInt) % p;
            == (SumOfPalindromes(i - 1) % p + StringToInt(IntToString(i) + ReverseString(IntToString(i))) % p) % p;
            == (SumOfPalindromes(i - 1) + StringToInt(IntToString(i) + ReverseString(IntToString(i)))) % p
            { ModuloProperty(SumOfPalindromes(i - 1), StringToInt(IntToString(i) + ReverseString(IntToString(i))), p); };
            == SumOfPalindromes(i) % p;
        }
        i := i + 1;
    }
    result := sum;
}
// </vc-code>

