function is_palindrome(n: nat) : bool {
  var s := natToString(n);
  forall i | 0 <= i < |s| :: s[i] == s[|s|-1-i]
}

// <vc-helpers>
lemma palindrome_sets_finite(n: nat)
  ensures |set i | 0 <= i <= n && i % 2 == 0 && is_palindrome(i)| < n + 2
  ensures |set i | 0 <= i <= n && i % 2 == 1 && is_palindrome(i)| < n + 2
{
  var even_set := set i | 0 <= i <= n && i % 2 == 0 && is_palindrome(i);
  var odd_set := set i | 0 <= i <= n && i % 2 == 1 && is_palindrome(i);
  var all_even := set i | 0 <= i <= n && i % 2 == 0;
  var all_odd := set i | 0 <= i <= n && i % 2 == 1;
  
  assert forall j :: j in all_even ==> 0 <= j <= n && j % 2 == 0;
  assert forall j :: j in all_odd ==> 0 <= j <= n && j % 2 == 1;
  
  if n == 0 {
    assert all_even == {0};
    assert all_odd == {};
    assert |all_even| == 1;
    assert |all_odd| == 0;
  } else if n == 1 {
    assert all_even == {0};
    assert all_odd == {1};
    assert |all_even| == 1;
    assert |all_odd| == 1;
  } else {
    if n % 2 == 0 {
      assert all_even == set k | 0 <= k <= n/2 :: 2*k;
      assert all_odd == set k | 0 <= k < n/2 :: 2*k+1;
      assert |all_even| == n / 2 + 1;
      assert |all_odd| == n / 2;
    } else {
      assert all_even == set k | 0 <= k <= (n-1)/2 :: 2*k;
      assert all_odd == set k | 0 <= k <= (n-1)/2 :: 2*k+1;
      assert |all_even| == (n + 1) / 2;
      assert |all_odd| == (n + 1) / 2;
    }
  }
  
  assert even_set <= all_even;
  assert odd_set <= all_odd;
  assert |even_set| <= |all_even|;
  assert |odd_set| <= |all_odd|;
}

lemma set_cardinality_helper(i: nat, is_pal: bool)
  requires is_pal == is_palindrome(i)
  ensures is_pal && i % 2 == 0 ==> 
    (set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j)) == 
    (set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j)) + {i}
  ensures is_pal && i % 2 == 1 ==> 
    (set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j)) == 
    (set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j)) + {i}
  ensures is_pal && i % 2 == 0 ==> 
    (set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j)) == 
    (set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j))
  ensures is_pal && i % 2 == 1 ==> 
    (set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j)) == 
    (set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j))
  ensures !is_pal ==> 
    (set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j)) == 
    (set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j))
  ensures !is_pal ==> 
    (set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j)) == 
    (set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j))
{
  var prev_even := set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j);
  var prev_odd := set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j);
  var new_even := set j | 0 <= j < i + 1 && j % 2 == 0 && is_palindrome(j);
  var new_odd := set j | 0 <= j < i + 1 && j % 2 == 1 && is_palindrome(j);
  
  if is_pal {
    if i % 2 == 0 {
      assert 0 <= i < i + 1 && i % 2 == 0 && is_palindrome(i);
      assert i in new_even;
      assert !(0 <= i < i && i % 2 == 0 && is_palindrome(i));
      assert i !in prev_even;
      assert new_even == prev_even + {i};
      assert new_odd == prev_odd;
    } else {
      assert 0 <= i < i + 1 && i % 2 == 1 && is_palindrome(i);
      assert i in new_odd;
      assert !(0 <= i < i && i % 2 == 1 && is_palindrome(i));
      assert i !in prev_odd;
      assert new_odd == prev_odd + {i};
      assert new_even == prev_even;
    }
  } else {
    assert !is_palindrome(i);
    assert !(0 <= i < i + 1 && i % 2 == 0 && is_palindrome(i));
    assert !(0 <= i < i + 1 && i % 2 == 1 && is_palindrome(i));
    assert i !in new_even;
    assert i !in new_odd;
    assert new_even == prev_even;
    assert new_odd == prev_odd;
  }
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
  palindrome_sets_finite(n);
  
  even := 0;
  odd := 0;
  
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant even == |set j | 0 <= j < i && j % 2 == 0 && is_palindrome(j)|
    invariant odd == |set j | 0 <= j < i && j % 2 == 1 && is_palindrome(j)|
  {
    var is_pal := is_palindrome(i);
    set_cardinality_helper(i, is_pal);
    
    if is_pal {
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
  assert (set j | 0 <= j < n + 1 && j % 2 == 0 && is_palindrome(j)) == (set j | 0 <= j <= n && j % 2 == 0 && is_palindrome(j));
  assert (set j | 0 <= j < n + 1 && j % 2 == 1 && is_palindrome(j)) == (set j | 0 <= j <= n && j % 2 == 1 && is_palindrome(j));
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