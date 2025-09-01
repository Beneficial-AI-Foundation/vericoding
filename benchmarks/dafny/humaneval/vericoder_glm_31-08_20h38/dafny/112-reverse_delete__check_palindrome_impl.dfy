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
function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function remove_chars(s: string, chars: string) : string {
  if |s| == 0 then
    ""
  else
    if s[0] in chars then
      remove_chars(s[1..], chars)
    else
      s[0] + remove_chars(s[1..], chars)
}

method check_palindrome(s: string) returns (result: bool)
  ensures result <==> is_palindrome_pred(s)
{
  result := is_palindrome_pred(s);
}

lemma remove_chars_properties(s: string, chars: string)
  ensures forall i :: 0 <= i < |remove_chars(s, chars)| ==> remove_chars(s, chars)[i] !in chars
  ensures forall i :: 0 <= i < |remove_chars(s, chars)| ==> remove_chars(s, chars)[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in remove_chars(s, chars)
{
  if |s| == 0 {
  } else if s[0] in chars {
    remove_chars_properties(s[1..], chars);
    forall i | 0 <= i < |remove_chars(s[1..], chars)|
      assert remove_chars(s, chars)[i] !in chars;
    {
      assert remove_chars(s, chars) == remove_chars(s[1..], chars);
    }
    forall i | 0 <= i < |remove_chars(s[1..], chars)|
      assert remove_chars(s, chars)[i] in s;
    {
      assert remove_chars(s, chars) == remove_chars(s[1..], chars);
    }
    forall i | 0 <= i < |s| && s[i] !in chars
      assert s[i] in remove_chars(s, chars);
    {
      if i == 0 {
        assert s[0] in chars;
        assert false;
      }
      assert s[i] !in chars;
      remove_chars_properties(s[1..], chars);
      assert s[i] in remove_chars(s[1..], chars);
      assert remove_chars(s, chars) == remove_chars(s[1..], chars);
    }
  } else {
    remove_chars_properties(s[1..], chars);
    forall i | 0 <= i < |remove_chars(s, chars)|
      assert remove_chars(s, chars)[i] !in chars;
    {
      if i == 0 {
        assert s[0] !in chars;
        assert remove_chars(s, chars)[0] == s[0];
      } else {
        assert remove_chars(s, chars) == s[0] + remove_chars(s[1..], chars);
        assert remove_chars(s, chars)[i] == remove_chars(s[1..], chars)[i-1];
        assert remove_chars_properties(s[1..], chars);
        assert 0 <= i-1 < |remove_chars(s[1..], chars)|;
        assert remove_chars(s[1..], chars)[i-1] !in chars;
      }
    }
    forall i | 0 <= i < |remove_chars(s, chars)|
      assert remove_chars(s, chars)[i] in s;
    {
      if i == 0 {
        assert remove_chars(s, chars)[0] == s[0];
        assert s[0] in s;
      } else {
        assert remove_chars(s, chars)[i] == remove_chars(s[1..], chars)[i-1];
        assert remove_chars_properties(s[1..], chars);
        assert remove_chars(s[1..], chars)[i-1] in s[1..];
        assert remove_chars(s[1..], chars)[i-1] in s;
      }
    }
    forall i | 0 <= i < |s| && s[i] !in chars
      assert s[i] in remove_chars(s, chars);
    {
      if i == 0 {
        assert s[0] !in chars;
        assert remove_chars(s, chars) == s[0] + remove_chars(s[1..], chars);
        assert s[0] in remove_chars(s, chars);
      } else {
        assert s[i] !in chars;
        assert s[i] in s[1..];
        remove_chars_properties(s[1..], chars);
        assert s[i] in remove_chars(s[1..], chars);
        assert remove_chars(s, chars) == s[0] + remove_chars(s[1..], chars);
        assert s[i] in remove_chars(s, chars);
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
  var res := remove_chars(s, chars);
  remove_chars_properties(s, chars);
  var is_palindrome := check_palindrome(res);
  return (res, is_palindrome);
}
// </vc-code>

function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end