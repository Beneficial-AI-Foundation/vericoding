

// <vc-helpers>
lemma palindrome_empty()
  ensures is_palindrome_pred("")
{
}

lemma palindrome_single(c: char)
  ensures is_palindrome_pred([c])
{
}

lemma palindrome_preserved_when_filtering(s: string, chars: string)
  requires is_palindrome_pred(s)
  ensures is_palindrome_pred(filter_chars(s, chars))
{
  var filtered := filter_chars(s, chars);
  if |filtered| <= 1 {
    return;
  }
  
  forall k | 0 <= k < |filtered|
    ensures filtered[k] == filtered[|filtered| - 1 - k]
  {
    var left_char := filtered[k];
    var right_char := filtered[|filtered| - 1 - k];
    
    var left_pos := find_original_position(s, chars, k);
    var right_pos := find_original_position(s, chars, |filtered| - 1 - k);
    
    assert s[left_pos] == left_char;
    assert s[right_pos] == right_char;
    assert s[left_pos] == s[|s| - 1 - left_pos];
    assert s[right_pos] == s[|s| - 1 - right_pos];
  }
}

function filter_chars(s: string, chars: string): string
{
  if |s| == 0 then ""
  else if s[0] in chars then filter_chars(s[1..], chars)
  else [s[0]] + filter_chars(s[1..], chars)
}

function find_original_position(s: string, chars: string, filtered_index: nat): nat
  requires filtered_index < |filter_chars(s, chars)|
  ensures find_original_position(s, chars, filtered_index) < |s|
  ensures s[find_original_position(s, chars, filtered_index)] !in chars
{
  find_original_position_helper(s, chars, filtered_index, 0)
}

function find_original_position_helper(s: string, chars: string, target_index: nat, current_pos: nat): nat
  requires current_pos <= |s|
  requires target_index < |filter_chars(s[current_pos..], chars)|
  ensures find_original_position_helper(s, chars, target_index, current_pos) >= current_pos
  ensures find_original_position_helper(s, chars, target_index, current_pos) < |s|
  decreases |s| - current_pos
{
  if current_pos >= |s| then current_pos
  else if s[current_pos] !in chars then
    if target_index == 0 then current_pos
    else find_original_position_helper(s, chars, target_index - 1, current_pos + 1)
  else find_original_position_helper(s, chars, target_index, current_pos + 1)
}
// </vc-helpers>

// <vc-spec>
method reverse_delete(s: string, chars: string) returns (res: string, is_palindrome: bool)
  // post-conditions-start
  ensures forall i :: 0 <= i < |res| ==> res[i] !in chars
  ensures forall i :: 0 <= i < |res| ==> res[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] !in chars ==> s[i] in res
  ensures is_palindrome <==> is_palindrome_pred(res)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  res := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |res| ==> res[j] !in chars
    invariant forall j :: 0 <= j < |res| ==> res[j] in s
    invariant forall j :: 0 <= j < i && s[j] !in chars ==> s[j] in res
    invariant res == filter_chars(s[..i], chars)
  {
    if s[i] !in chars {
      res := res + [s[i]];
    }
    i := i + 1;
  }
  
  is_palindrome := true;
  i := 0;
  while i < |res| / 2
    invariant 0 <= i <= |res| / 2
    invariant is_palindrome <==> (forall k :: 0 <= k < i ==> res[k] == res[|res| - 1 - k])
  {
    if res[i] != res[|res| - 1 - i] {
      is_palindrome := false;
    }
    i := i + 1;
  }
}
// </vc-code>

method check_palindrome(s: string) returns (result: bool)
  // post-conditions-start
  ensures result <==> is_palindrome_pred(s)
  // post-conditions-end
{
  assume{:axiom} false;
}
function is_palindrome_pred(s : string) : bool {
  forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
// pure-end