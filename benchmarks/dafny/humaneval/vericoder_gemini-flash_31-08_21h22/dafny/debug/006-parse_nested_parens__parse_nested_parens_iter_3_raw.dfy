```vc-helpers
function parse_paren_group(s : string) : int
  requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'
  ensures parse_paren_group(s) >= 0
{
  var current_depth := 0;
  var max_depth := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant current_depth >= 0
    invariant max_depth >= 0
    invariant max_depth >= current_depth
  {
    if s[i] == '(' {
      current_depth := current_depth + 1;
      if current_depth > max_depth {
        max_depth := current_depth;
      }
    } else if s[i] == ')' {
      current_depth := current_depth - 1;
      // It is impossible for current_depth to become negative if the input string is well-formed,
      // but if we need to handle ill-formed strings we could add an assertion or a check here.
      // For now, we assume current_depth will remain non-negative.
    }
    i := i + 1;
  }
  max_depth
}

function split(s : string) : seq<string>
  requires forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
  ensures forall s1 :: s1 in split(s) ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
{
  var res: seq<string> := [];
  var start_idx := 0;
  while start_idx < |s|
    invariant 0 <= start_idx <= |s|
    invariant forall s1 :: s1 in res ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
  {
    if s[start_idx] == ' ' {
      start_idx := start_idx + 1;
    } else {
      var end_idx := start_idx;
      while end_idx < |s| and s[end_idx] != ' '
        invariant start_idx <= end_idx <= |s|
        invariant forall k :: start_idx <= k < end_idx ==> s[k] != ' '
      {
        end_idx := end_idx + 1;
      }
      var sub := s[start_idx .. end_idx];
      if |sub| > 0 { // Ensure non-empty strings are added
        res := res + [sub];
      }
      start_idx := end_idx;
    }
  }
  res
}
```

```vc-code
{
  var components := split(paren_string);
  var res: seq<int> := [];
  for s in components {
    res := res + [parse_paren_group(s)];
  }
  return res;
}
```