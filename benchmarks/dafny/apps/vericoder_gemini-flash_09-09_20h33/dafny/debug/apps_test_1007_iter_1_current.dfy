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
function ModuloSum(a: int, b: int, p: int): int
    requires p > 0
    ensures 0 <= ModuloSum(a, b, p) < p
    ensures ModuloSum(a, b, p) == (a + b) % p
{
    (a + b) % p
}

function ModuloSumSeq(seq_val: seq<int>, p: int): int
    requires forall i :: 0 <= i < |seq_val| ==> seq_val[i] >= 0
    requires p > 0
    decreases |seq_val|
    ensures 0 <= ModuloSumSeq(seq_val, p) < p
    ensures ModuloSumSeq(seq_val, p) == (seq_val[0] + (if |seq_val| > 1 then ModuloSumSeq(seq_val[1..], p) else 0)) % p
{
    if |seq_val| == 0 then 0
    else (seq_val[0] + ModuloSumSeq(seq_val[1..], p)) % p
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
    for i := 1 to k
        invariant 0 <= sum < p
        invariant sum == (SumOfPalindromes(i-1) % p)
    {
        var s := IntToString(i);
        var reversed := ReverseString(s);
        var palindrome_str := s + reversed;
        var palindrome_int := StringToInt(palindrome_str);
        sum := (sum + palindrome_int) % p;
    }
    return sum;
}
// </vc-code>

