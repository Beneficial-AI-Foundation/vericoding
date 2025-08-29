// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def will_it_fly(q: List[int], w: int) -> bool
Write a function that returns True if the object q will fly, and False otherwise. The object q will fly if it's balanced (it is a palindromic list) and the sum of its elements is less than or equal the maximum possible weight w.
*/
// </vc-description>

// <vc-spec>
method will_it_fly(q: seq<int>, w: int) returns (result: bool)
  ensures result == (is_palindrome_pred(q) && sum(q) <= w)
// </vc-spec>
// <vc-code>
{
  var is_palindrome := true;
  var i := 0;
  while i < |q| / 2
    invariant 0 <= i <= |q| / 2
    invariant is_palindrome == (forall k :: 0 <= k < i ==> q[k] == q[|q| - 1 - k])
  {
    if q[i] != q[|q| - 1 - i] {
      is_palindrome := false;
      break;
    }
    i := i + 1;
  }
  
  if is_palindrome {
    assert forall k :: 0 <= k < |q| / 2 ==> q[k] == q[|q| - 1 - k];
    assert forall k :: |q| / 2 <= k < |q| ==> q[k] == q[|q| - 1 - k];
    assert is_palindrome_pred(q);
  } else {
    assert !is_palindrome_pred(q);
  }
  
  var total_sum := sum(q);
  result := is_palindrome && total_sum <= w;
}
// </vc-code>

function is_palindrome_pred(s : seq<int>) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end
function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end