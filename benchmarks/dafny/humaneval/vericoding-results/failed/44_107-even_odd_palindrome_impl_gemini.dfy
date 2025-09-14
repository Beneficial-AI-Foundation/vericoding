// <vc-preamble>
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

function is_palindrome(n: nat) : bool {
  var s := natToString(n);
  forall i | 0 <= i < |s| :: s[i] == s[|s|-1-i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed predicate syntax by adding 'in' */
predicate is_palindrome_pred(n: nat) {
  let s := natToString(n) in
  forall i | 0 <= i < |s| :: s[i] == s[|s|-1-i]
}

lemma is_palindrome_equivalence(n: nat)
  ensures is_palindrome(n) <==> is_palindrome_pred(n)
{ }
// </vc-helpers>

// <vc-spec>
method even_odd_palindrome(n: nat) returns (even: nat, odd: nat)

  ensures even == |set i | 0 <= i <= n && i % 2 == 0 && is_palindrome(i)|
  ensures odd == |set i | 0 <= i <= n && i % 2 == 1 && is_palindrome(i)|
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no changes, logic from previous iteration is sound */
{
  even := 0;
  odd := 0;
  var i: nat := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant even == |set j | 0 <= j < i && j % 2 == 0 && is_palindrome_pred(j)|
    invariant odd == |set j | 0 <= j < i && j % 2 == 1 && is_palindrome_pred(j)|
    decreases n - i
  {
    is_palindrome_equivalence(i);
    if is_palindrome(i) {
      if i % 2 == 0 {
        even := even + 1;
      } else {
        odd := odd + 1;
      }
    }
    i := i + 1;
  }

  forall j | 0 <= j <= n 
    ensures is_palindrome(j) <==> is_palindrome_pred(j)
  {
    is_palindrome_equivalence(j);
  }
}
// </vc-code>
