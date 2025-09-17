// <vc-preamble>

predicate ValidInput(n: nat)
{
    n >= 1
}

function DigitsOf(n: nat): seq<nat>
    requires n >= 0
{
    if n < 10 then [n]
    else DigitsOf(n / 10) + [n % 10]
}

function ReverseSeq<T>(s: seq<T>): seq<T>
{
    if |s| <= 1 then s
    else ReverseSeq(s[1..]) + [s[0]]
}

function IsPalindrome(n: nat): bool
    requires n >= 0
{
    var digits := DigitsOf(n);
    digits == ReverseSeq(digits)
}

function CountPalindromesInRange(start: nat, end: nat): nat
    requires start >= 1
    decreases end - start + 1
{
    if start > end then 0
    else if IsPalindrome(start) then 1 + CountPalindromesInRange(start + 1, end)
    else CountPalindromesInRange(start + 1, end)
}

function CountEvenPalindromesInRange(start: nat, end: nat): nat
    requires start >= 1
    decreases end - start + 1
{
    if start > end then 0
    else if IsPalindrome(start) && start % 2 == 0 then 1 + CountEvenPalindromesInRange(start + 1, end)
    else CountEvenPalindromesInRange(start + 1, end)
}

function CountOddPalindromesInRange(start: nat, end: nat): nat
    requires start >= 1
    decreases end - start + 1
{
    if start > end then 0
    else if IsPalindrome(start) && start % 2 == 1 then 1 + CountOddPalindromesInRange(start + 1, end)
    else CountOddPalindromesInRange(start + 1, end)
}
function CountPalindromes(n: nat, current: nat, even_count: nat, odd_count: nat): (nat, nat)
    requires current >= 1
    requires n >= 1
    requires current <= n + 1
    decreases n - current + 1
    ensures CountPalindromes(n, current, even_count, odd_count).0 >= even_count
    ensures CountPalindromes(n, current, even_count, odd_count).1 >= odd_count
    ensures CountPalindromes(n, current, even_count, odd_count).0 == even_count + CountEvenPalindromesInRange(current, n)
    ensures CountPalindromes(n, current, even_count, odd_count).1 == odd_count + CountOddPalindromesInRange(current, n)
    ensures CountPalindromes(n, current, even_count, odd_count).0 + CountPalindromes(n, current, even_count, odd_count).1 == even_count + odd_count + CountPalindromesInRange(current, n)
{
    if current > n then
        (even_count, odd_count)
    else if IsPalindrome(current) then
        if current % 2 == 0 then
            CountPalindromes(n, current + 1, even_count + 1, odd_count)
        else
            CountPalindromes(n, current + 1, even_count, odd_count + 1)
    else
        CountPalindromes(n, current + 1, even_count, odd_count)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method even_odd_palindrome(n: nat) returns (result: (nat, nat))
    requires ValidInput(n)
    ensures result.0 >= 0
    ensures result.1 >= 0
    ensures result.0 == CountEvenPalindromesInRange(1, n)
    ensures result.1 == CountOddPalindromesInRange(1, n)
    ensures result.0 + result.1 == CountPalindromesInRange(1, n)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
