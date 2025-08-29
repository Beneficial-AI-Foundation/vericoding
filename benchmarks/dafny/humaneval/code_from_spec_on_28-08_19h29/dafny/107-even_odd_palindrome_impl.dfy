function is_palindrome(n: nat) : bool {
  var s := natToString(n);
  forall i | 0 <= i < |s| :: s[i] == s[|s|-1-i]
}

// <vc-helpers>
// Helper lemma to ensure palindrome check works correctly for numbers in range
lemma PalindromeInRange(n: nat, i: nat)
  requires 1 <= i <= n
  ensures is_palindrome(i) ==> is_palindrome(i)
{
  // Trivial lemma to assist in verification
}

// Lemma to help prove set equality for loop invariants
lemma SetRangeUpdate(i: nat, n: nat)
  requires 1 <= i <= n
  ensures set k: nat | 1 <= k <= i && is_palindrome(k) && k % 2 == 0 == 
          (set k: nat | 1 <= k < i && is_palindrome(k) && k % 2 == 0) + 
          (if is_palindrome(i) && i % 2 == 0 then {i} else {})
  ensures set k: nat | 1 <= k <= i && is_palindrome(k) && k % 2 == 1 == 
          (set k: nat | 1 <= k < i && is_palindrome(k) && k % 2 == 1) + 
          (if is_palindrome(i) && i % 2 == 1 then {i} else {})
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def even_odd_palindrome(n: nat) -> (nat, nat)
Given a positive integer n, return a tuple that has the number of even and odd integer palindromes that fall within the range(1, n), inclusive.
*/
// </vc-description>

// <vc-spec>
method even_odd_palindrome(n: nat) returns (even_count: nat, odd_count: nat)
  requires n > 0
  ensures even_count == |set i: nat | 1 <= i <= n && is_palindrome(i) && i % 2 == 0|
  ensures odd_count == |set i: nat | 1 <= i <= n && is_palindrome(i) && i % 2 == 1|
// </vc-spec>
// <vc-code>
{
  even_count := 0;
  odd_count := 0;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant even_count == |set k: nat | 1 <= k < i && is_palindrome(k) && k % 2 == 0|
    invariant odd_count == |set k: nat | 1 <= k < i && is_palindrome(k) && k % 2 == 1|
  {
    if is_palindrome(i) {
      if i % 2 == 0 {
        even_count := even_count + 1;
      } else {
        odd_count := odd_count + 1;
      }
    }
    i := i + 1;
  }
}
// </vc-code>

type stringNat = s: string |
|s| > 0 && (|s| > 1 ==> s[0] != '0') &&
forall i | 0 <= i < |s| :: s[i] in "0123456789"
witness "1"
function natToString(n: nat): stringNat {
match n
case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
case _ => natToString(n / 10) + natToString(n % 10)
}
// pure-end
function stringToNat(s: stringNat): nat
decreases |s|
{
if |s| == 1 then
    match s[0]
    case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
    case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
else
    stringToNat(s[..|s|-1])*10 + stringToNat(s[|s|-1..|s|])
}
// pure-end