function is_palindrome(n: nat) : bool {
  var s := natToString(n);
  forall i | 0 <= i < |s| :: s[i] == s[|s|-1-i]
}

// <vc-helpers>
lemma {:axiom} CountEvenPalindromes(n: nat, even_count: nat)
  requires even_count == |set i | 0 <= i <= n && i % 2 == 0 && is_palindrome(i)|
  ensures even_count >= 0

lemma {:axiom} CountOddPalindromes(n: nat, odd_count: nat)
  requires odd_count == |set i | 0 <= i <= n && i % 2 == 1 && is_palindrome(i)|
  ensures odd_count >= 0

lemma {:axiom} PalindromeCountInvariant(k: nat, n: nat, even_so_far: nat, odd_so_far: nat)
  requires k <= n + 1
  requires even_so_far == |set i | 0 <= i < k && i % 2 == 0 && is_palindrome(i)|
  requires odd_so_far == |set i | 0 <= i < k && i % 2 == 1 && is_palindrome(i)|
  ensures even_so_far >= 0 && odd_so_far >= 0

lemma SetEquality(n: nat)
  ensures (set i | 0 <= i <= n && i % 2 == 0 && is_palindrome(i)) == (set i | 0 <= i < n + 1 && i % 2 == 0 && is_palindrome(i))
  ensures (set i | 0 <= i <= n && i % 2 == 1 && is_palindrome(i)) == (set i | 0 <= i < n + 1 && i % 2 == 1 && is_palindrome(i))
{
}

lemma SetAddition(i: nat, s1: set<nat>, s2: set<nat>)
  requires i % 2 == 0
  requires is_palindrome(i)
  requires s1 == (set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j))
  requires s2 == (set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j))
  ensures s2 == s1 + {i}
  ensures |s2| == |s1| + 1
{
}

lemma SetAdditionOdd(i: nat, s1: set<nat>, s2: set<nat>)
  requires i % 2 == 1
  requires is_palindrome(i)
  requires s1 == (set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j))
  requires s2 == (set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j))
  ensures s2 == s1 + {i}
  ensures |s2| == |s1| + 1
{
}

lemma SetNoAddition(i: nat, s1: set<nat>, s2: set<nat>)
  requires !is_palindrome(i)
  requires s1 == (set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j))
  requires s2 == (set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j))
  ensures s2 == s1
  ensures |s2| == |s1|
{
}

lemma SetNoAdditionOdd(i: nat, s1: set<nat>, s2: set<nat>)
  requires !is_palindrome(i)
  requires s1 == (set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j))
  requires s2 == (set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j))
  ensures s2 == s1
  ensures |s2| == |s1|
{
}

lemma MaintainEvenInvariant(i: nat, even: nat, odd: nat)
  requires even == |set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j)|
  requires odd == |set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j)|
  ensures (is_palindrome(i) && i % 2 == 0) ==> (even + 1) == |set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j)|
  ensures (is_palindrome(i) && i % 2 == 1) ==> even == |set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j)|
  ensures (!is_palindrome(i)) ==> even == |set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j)|
{
  var s1 := set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j);
  var s2 := set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j);
  
  if is_palindrome(i) && i % 2 == 0 {
    SetAddition(i, s1, s2);
  } else {
    SetNoAddition(i, s1, s2);
  }
}

lemma MaintainOddInvariant(i: nat, even: nat, odd: nat)
  requires even == |set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j)|
  requires odd == |set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j)|
  ensures (is_palindrome(i) && i % 2 == 1) ==> (odd + 1) == |set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j)|
  ensures (is_palindrome(i) && i % 2 == 0) ==> odd == |set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j)|
  ensures (!is_palindrome(i)) ==> odd == |set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j)|
{
  var s1 := set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j);
  var s2 := set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j);
  
  if is_palindrome(i) && i % 2 == 1 {
    SetAdditionOdd(i, s1, s2);
  } else {
    SetNoAdditionOdd(i, s1, s2);
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def even_odd_palindrome(n: nat) -> (nat, nat)
Given a positive integer n, return a tuple that has the number of even and odd integer palindromes that fall within the range(1, n), inclusive.
*/
// </vc-description>

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
        MaintainEvenInvariant(i, even, odd);
        SetAddition(i, set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j), set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j));
        even := even + 1;
      } else {
        MaintainOddInvariant(i, even, odd);
        SetAdditionOdd(i, set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j), set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j));
        odd := odd + 1;
      }
    } else {
      MaintainEvenInvariant(i, even, odd);
      MaintainOddInvariant(i, even, odd);
      SetNoAddition(i, set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j), set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j));
      SetNoAdditionOdd(i, set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j), set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j));
    }
    i := i + 1;
  }
  
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