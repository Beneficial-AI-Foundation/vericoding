This verification task implements a function to count even and odd palindromic integers in the range [1, n] inclusive. A palindromic integer reads the same forwards and backwards (e.g., 121, 7, 1331). The function should return a tuple (even_count, odd_count) representing the counts of even and odd palindromic integers respectively.

// ======= TASK =======
// Given a positive integer n, count the number of even and odd palindromic integers in the range [1, n] inclusive.
// A palindromic integer reads the same forwards and backwards (e.g., 121, 7, 1331).
// Return a tuple (even_count, odd_count) where even_count is the number of even palindromic integers
// and odd_count is the number of odd palindromic integers in [1, n].

// ======= SPEC REQUIREMENTS =======
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

// ======= HELPERS =======
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

// ======= MAIN METHOD =======
function even_odd_palindrome(n: nat): (nat, nat)
    requires ValidInput(n)
    ensures even_odd_palindrome(n).0 >= 0
    ensures even_odd_palindrome(n).1 >= 0
    ensures even_odd_palindrome(n).0 == CountEvenPalindromesInRange(1, n)
    ensures even_odd_palindrome(n).1 == CountOddPalindromesInRange(1, n)
    ensures even_odd_palindrome(n).0 + even_odd_palindrome(n).1 == CountPalindromesInRange(1, n)
{
    var result := CountPalindromes(n, 1, 0, 0);
    result
}
