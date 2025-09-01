function is_palindrome(n: nat) : bool {
  var s := natToString(n);
  forall i | 0 <= i < |s| :: s[i] == s[|s|-1-i]
}

// <vc-helpers>
lemma PalindromeSetFinite(n: nat)
  ensures |set i | 0 <= i <= n && i % 2 == 0 && is_palindrome(i)| < n + 1
  ensures |set i | 0 <= i <= n && i % 2 == 1 && is_palindrome(i)| < n + 1
{
  var evenSet := set i | 0 <= i <= n && i % 2 == 0 && is_palindrome(i);
  var oddSet := set i | 0 <= i <= n && i % 2 == 1 && is_palindrome(i);
  var allSet := set i | 0 <= i <= n;
  
  assert evenSet <= allSet;
  assert oddSet <= allSet;
  assert |allSet| == n + 1;
}

lemma SetEquality(n: nat)
  ensures set j | 0 <= j < n + 1 && j % 2 == 0 && is_palindrome(j) == set j | 0 <= j <= n && j % 2 == 0 && is_palindrome(j)
  ensures set j | 0 <= j < n + 1 && j % 2 == 1 && is_palindrome(j) == set j | 0 <= j <= n && j % 2 == 1 && is_palindrome(j)
{
  var set1 := set j | 0 <= j < n + 1 && j % 2 == 0 && is_palindrome(j);
  var set2 := set j | 0 <= j <= n && j % 2 == 0 && is_palindrome(j);
  assert set1 == set2;
  
  var set3 := set j | 0 <= j < n + 1 && j % 2 == 1 && is_palindrome(j);
  var set4 := set j | 0 <= j <= n && j % 2 == 1 && is_palindrome(j);
  assert set3 == set4;
}
// </vc-helpers>

// <vc-spec>
method even_odd_palindrome(n: nat) returns (even: nat, odd: nat)
  // post-conditions-start
  ensures even == |set i | 0 <= i <= n && i % 2 == 0 && is_palindrome(i)|
  ensures odd == |set i | 0 <= i <= n && i % 2 == 1 && is_palindrome(i)|
// </vc-spec>
// <vc-code>
{
  even := 0;
  odd := 0;
  
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant even == |set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j)|
    invariant odd == |set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j)|
  {
    if is_palindrome(i) {
      if i % 2 == 0 {
        even := even + 1;
      } else {
        odd := odd + 1;
      }
    }
    i := i + 1;
  }
  
  assert i == n + 1;
  assert even == |set j | 0 <= j < n + 1 && j % 2 == 0 && is_palindrome(j)|;
  assert odd == |set j | 0 <= j < n + 1 && j % 2 == 1 && is_palindrome(j)|;
  
  SetEquality(n);
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