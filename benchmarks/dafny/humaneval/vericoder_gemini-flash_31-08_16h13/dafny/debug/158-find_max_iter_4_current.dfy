

// <vc-helpers>
function string_to_char_set(s: string): set<char>
{
  set c | c in s
}
// </vc-helpers>

// <vc-spec>
method find_max(strings : seq<string>) returns (s : string)
   // pre-conditions-start
    requires |strings| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures s in strings
    ensures forall i : int :: 0 <= i < |strings| ==> |set c | c in s| >= |set c | c in strings[i]|
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var max_s := strings[0];
  var max_len_distinct_chars := |string_to_char_set(strings[0])|;

  for i := 1 to |strings| - 1
    invariant 0 < |strings|
    invariant 0 <= i <= |strings|
    invariant max_s in strings[..i]
    invariant forall j : int :: 0 <= j < i ==> max_len_distinct_chars >= |string_to_char_set(strings[j])|
    invariant max_len_distinct_chars == |string_to_char_set(max_s)|
    invariant i > 0 ==> strings[0] in strings[..i]
    invariant forall k : int :: 0 <= k < i ==> max_s in strings[0..i]
    invariant forall k : int :: 0 <= k < i ==> max_s == strings[L_max_s_index(strings, i, max_s)]
    invariant L_max_s_index(strings, i, max_s) < i
  {
    var current_s := strings[i];
    var current_len_distinct_chars := |string_to_char_set(current_s)|;

    if current_len_distinct_chars > max_len_distinct_chars {
      max_len_distinct_chars := current_len_distinct_chars;
      max_s := current_s;
    } 
  }
  s := max_s;
}
// </vc-code>

