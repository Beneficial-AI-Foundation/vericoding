function is_palindrome(n: nat) : bool {
  var s := natToString(n);
  forall i | 0 <= i < |s| :: s[i] == s[|s|-1-i]
}

// <vc-helpers>
lemma PalindromeCountProperties(n: nat, even_count: nat, odd_count: nat)
  requires even_count == |set i | 1 <= i <= n && is_palindrome(i) && i % 2 == 0|
  requires odd_count == |set i | 1 <= i <= n && is_palindrome(i) && i % 2 == 1|
  ensures even_count + odd_count == |set i | 1 <= i <= n && is_palindrome(i)|
{
  var all_palindromes := set i | 1 <= i <= n && is_palindrome(i);
  var even_palindromes := set i | 1 <= i <= n && is_palindrome(i) && i % 2 == 0;
  var odd_palindromes := set i | 1 <= i <= n && is_palindrome(i) && i % 2 == 1;
  
  assert all_palindromes == even_palindromes + odd_palindromes;
  assert even_palindromes * odd_palindromes == {};
}

lemma LoopInvariantHelper(n: nat, i: nat, even_count: nat, odd_count: nat)
  requires 1 <= i <= n + 1
  requires even_count == |set j | 1 <= j < i && is_palindrome(j) && j % 2 == 0|
  requires odd_count == |set j | 1 <= j < i && is_palindrome(j) && j % 2 == 1|
  requires i <= n
  ensures even_count == |set j | 1 <= j <= i && is_palindrome(j) && j % 2 == 0| - (if is_palindrome(i) && i % 2 == 0 then 1 else 0)
  ensures odd_count == |set j | 1 <= j <= i && is_palindrome(j) && j % 2 == 1| - (if is_palindrome(i) && i % 2 == 1 then 1 else 0)
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
method even_odd_palindrome(n: nat) returns (even_result: nat, odd_result: nat)
  ensures even_result == |set i | 1 <= i <= n && is_palindrome(i) && i % 2 == 0|
  ensures odd_result == |set i | 1 <= i <= n && is_palindrome(i) && i % 2 == 1|
// </vc-spec>
// <vc-code>
{
  var even_count := 0;
  var odd_count := 0;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant even_count == |set j | 1 <= j < i && is_palindrome(j) && j % 2 == 0|
    invariant odd_count == |set j | 1 <= j < i && is_palindrome(j) && j % 2 == 1|
    decreases n - i + 1
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
  
  even_result := even_count;
  odd_result := odd_count;
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