function is_palindrome(n: nat) : bool {
  var s := natToString(n);
  forall i | 0 <= i < |s| :: s[i] == s[|s|-1-i]
}

// <vc-helpers>
lemma palindrome_count_property(n: nat, even_count: nat, odd_count: nat)
  ensures even_count == |set i | 0 <= i <= n && i % 2 == 0 && is_palindrome(i)| &&
           odd_count == |set i | 0 <= i <= n && i % 2 == 1 && is_palindrome(i)|
{
}

lemma palindrome_zero_even()
  ensures is_palindrome(0) && 0 % 2 == 0
{
}

lemma palindrome_single_digit(d: nat)
  requires d < 10
  ensures is_palindrome(d)
{
}

lemma palindrome_even_odd_property(i: nat)
  ensures (i % 2 == 0 && is_palindrome(i)) ==> (i % 2 == 0)
  ensures (i % 2 == 1 && is_palindrome(i)) ==> (i % 2 == 1)
{
}

lemma set_extension_lemma(prev_i: nat, new_i: nat)
  requires new_i == prev_i + 1
  ensures |set j | 0 <= j < new_i && j % 2 == 0 && is_palindrome(j)| == 
           |set j | 0 <= j < prev_i && j % 2 == 0 && is_palindrome(j)| + 
           (if prev_i % 2 == 0 && is_palindrome(prev_i) then 1 else 0)
  ensures |set j | 0 <= j < new_i && j % 2 == 1 && is_palindrome(j)| == 
           |set j | 0 <= j < prev_i && j % 2 == 1 && is_palindrome(j)| + 
           (if prev_i % 2 == 1 && is_palindrome(prev_i) then 1 else 0)
{
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
    ghost var prev_i := i;
    
    if i % 2 == 0 && is_palindrome(i) {
      even := even + 1;
    }
    if i % 2 == 1 && is_palindrome(i) {
      odd := odd + 1;
    }
    i := i + 1;
    
    ghost set_extension_lemma(prev_i, i);
  }
  palindrome_count_property(n, even, odd);
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