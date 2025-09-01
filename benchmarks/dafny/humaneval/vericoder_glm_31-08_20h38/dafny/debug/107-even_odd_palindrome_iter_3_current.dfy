function is_palindrome(n: nat) : bool {
  var s := natToString(n);
  forall i | 0 <= i < |s| :: s[i] == s[|s|-1-i]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method even_odd_palindrome(n: nat) returns (even: nat, odd: nat)
  // post-conditions-start
  ensures even == |set i | 0 <= i <= n && i % 2 == 0 && is_palindrome(i)|
  ensures odd == |set i | 0 <= i <= n && i % 2 == 1 && is_palindrome(i)|
// </vc-spec>
// <vc-code>
{
    var even_count := 0;
    var odd_count := 0;
    if is_palindrome(0) {
        if 0 % 2 == 0 {
            even_count := even_count + 1;
        } else {
            odd_count := odd_count + 1;
        }
    }
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant even_count == |set j | 0 <= j <= i && j % 2 == 0 && is_palindrome(j)|
        invariant odd_count == |set j | 0 <= j <= i && j % 2 == 1 && is_palindrome
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