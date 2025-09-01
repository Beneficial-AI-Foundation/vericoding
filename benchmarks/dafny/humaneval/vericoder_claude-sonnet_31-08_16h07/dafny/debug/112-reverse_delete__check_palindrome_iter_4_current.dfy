method reverse_delete(s: string, chars: string) returns (res: string, is_palindrome: bool)
  // post-conditions-start
  ensures forall i :: 0 <= i < |res| ==> res[i] !in chars
  ensures forall i :: 0 <= i < |res| ==> res[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in res
  ensures is_palindrome <==> is_palindrome_pred(res)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma palindrome_empty()
  ensures is_palindrome_pred("")
{
}

lemma palindrome_single(c: char)
  ensures is_palindrome_pred([c])
{
}

lemma palindrome_check_helper(s: string, i: int, j: int)
  requires 0 <= i <= j < |s|
  requires forall k :: i <= k <= j ==> s[k] == s[j - k + i]
  ensures forall k :: i <= k <= j ==> s[k] == s[|s| - 1 - k] || s[k] == s[|s| - 1 - (j - k + i)]
{
  forall k | i <= k <= j
    ensures s[k] == s[|s| - 1 - k] || s[k] == s[|s| - 1 - (j - k + i)]
  {
    assert s[k] == s[j - k + i];
    assert s[k] == s[|s| - 1 - (j - k + i)];
  }
}

lemma palindrome_completeness(s: string, i: int)
  requires 0 <= i
  requires i >= |s| / 2
  requires |s| > 0
  requires forall k :: 0 <= k < i && k < |s| && |s| - 1 - k >= 0 && |s| - 1 - k < |s| ==> s[k] == s[|s| - 1 - k]
  ensures is_palindrome_pred(s)
{
  forall k | 0 <= k < |s|
    ensures s[k] == s[|s| - 1 - k]
  {
    if k < i {
      assert k < |s|;
      assert |s| - 1 - k >= 0;
      assert |s| - 1 - k < |s|;
      assert s[k] == s[|s| - 1 - k];
    } else {
      var mirror_k := |s| - 1 - k;
      assert mirror_k >= 0;
      assert k >= i;
      assert k < |s|;
      assert mirror_k < |s| - i;
      assert i >= |s| / 2;
      assert |s| - i <= |s| - |s| / 2;
      assert |s| - |s| / 2 <= |s| / 2 + 1;
      assert mirror_k < |s| / 2 + 1;
      assert mirror_k <= i;
      if mirror_k < i {
        assert mirror_k < |s|;
        assert |s| - 1 - mirror_k >= 0;
        assert |s| - 1 - mirror_k < |s|;
        assert s[mirror_k] == s[|s| - 1 - mirror_k];
        assert |s| - 1 - mirror_k == k;
        assert s[mirror_k] == s[k];
        assert s[k] == s[|s| - 1 - k];
      } else {
        assert mirror_k == i;
        assert k == |s| - 1 - i;
        if |s| % 2 == 1 {
          assert i == |s| / 2;
          assert k == |s| / 2;
          assert mirror_k == |s| / 2;
          assert s[k] == s[|s| - 1 - k];
        } else {
          assert false;
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method check_palindrome(s: string) returns (result: bool)
  // post-conditions-start
  ensures result <==> is_palindrome_pred(s)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    palindrome_empty();
    result := true;
    return;
  }
  
  if |s| == 1 {
    palindrome_single(s[0]);
    result := true;
    return;
  }
  
  var i := 0;
  var j := |s| - 1;
  
  while i < j
    invariant 0 <= i
    invariant j < |s|
    invariant i + j == |s| - 1
    invariant j >= 0
    invariant i <= |s|
    invariant forall k :: 0 <= k < i && k < |s| && |s| - 1 - k >= 0 && |s| - 1 - k < |s| ==> s[k] == s[|s| - 1 - k]
  {
    if s[i] != s[j] {
      result := false;
      return;
    }
    i := i + 1;
    j := j - 1;
  }
  
  palindrome_completeness(s, i);
  result := true;
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end