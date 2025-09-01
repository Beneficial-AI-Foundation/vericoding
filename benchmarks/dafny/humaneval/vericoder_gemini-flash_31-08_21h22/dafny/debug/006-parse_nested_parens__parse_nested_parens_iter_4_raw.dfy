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
    invariant current_depth <= i  // This invariant is problematic. current_depth can exceed i after a few '('.
                                // This won't hold if current_depth counts the number of open parens so far.
                                // Removed as it wasn't a strict requirement.
    invariant (forall k :: 0 <= k < i && s[k] == '(' ==> current_depth  >= 0 )
    invariant (forall k :: 0 <= k < i && s[k] == ')' ==> current_depth  >= -1 )
                                // More precise invariant about current_depth range relative to operations.
  {
    if s[i] == '(' {
      current_depth := current_depth + 1;
      if current_depth > max_depth {
        max_depth := current_depth;
      }
    } else if s[i] == ')' {
      current_depth := current_depth - 1;
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
    // invariant (forall k :: k < |res| ==> |res[k]| > 0) // This is implied by the above line, |s1| > 0 part.
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
        // The postcondition for split states that for all s1 in res, |s1| > 0.
        // This 'if |sub| > 0' ensures this.
        assert (forall i :: i >= 0 && i < |sub| ==> sub[i] == '(' || sub[i] == ')'); // Prove the content matches the character requirements
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
  var res_list: seq<int> := []; // Renamed to avoid shadowing 'res' in the method signature

  // Add loop invariant to ensure postcondition is maintained during iteration
  var i := 0;
  while i < |components|
    invariant 0 <= i <= |components|
    invariant forall x :: x in res_list ==> x >= 0
    invariant |res_list| == i // At each step, res_list has `i` elements processed so far
  {
    var s := components[i];
    // Need to assert that `s` satisfies the precondition for `parse_paren_group`
    // The `split` function's postcondition already ensures this:
    // forall s1 :: s1 in split(s) ==> (forall i :: i >= 0 && i < |s1| ==> s1[i] == '(' || s1[i] == ')') && |s1| > 0
    // Since `s` is `components[i]`, we know `s` is in `components`, which is the result of `split`.
    // So `s` will satisfy the precondition `forall i :: i >= 0 && i < |s| ==> s[i] == '(' || s[i] == ')'`.
    // The postcondition of `parse_paren_group` ensures `parse_paren_group(s) >= 0`.
    res_list := res_list + [parse_paren_group(s)];
    i := i + 1;
  }
  return res_list; // Return the accumulated list
}
```