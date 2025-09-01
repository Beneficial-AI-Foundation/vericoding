function ParenthesesDepth(s: string, i: int, j: int): int
    decreases j - i 
    requires 0 <= i <= j <= |s|
{
    if i == j then
        0
    else if s[i] == '(' then
        ParenthesesDepth(s, i+1, j) + 1
    else if s[i] == ')' then
        ParenthesesDepth(s, i+1, j) - 1
    else
        ParenthesesDepth(s, i+1, j)
}
function InnerDepthsPositive(s: string) : bool
{
    forall i :: 0 < i < |s| ==> ParenthesesDepth(s, 0, i) > 0
}
function InnerDepthsNonnegative(s: string) : bool
{
    forall i :: 0 < i < |s| ==> ParenthesesDepth(s, 0, i) >= 0
}

// <vc-helpers>
function is_balanced_and_positive(s: string): bool
  requires ParenthesesDepth(s, 0, |s|) == 0
  requires InnerDepthsNonnegative(s)
{
  ParenthesesDepth(s, 0, |s|) == 0 && (forall i :: 0 < i < |s| ==> ParenthesesDepth(s, 0, i) > 0)
}
// </vc-helpers>

// <vc-spec>
method separate_paren_groups(paren_string: string) returns (res : seq<string>)
    // pre-conditions-start
    requires ParenthesesDepth(paren_string, 0, |paren_string|) == 0
    requires InnerDepthsNonnegative(paren_string)
    // pre-conditions-end
    // post-conditions-start
    ensures forall k :: 0 <= k < |res| ==> ParenthesesDepth(res[k], 0, |res[k]|) == 0
    ensures forall k :: 0 <= k < |res| ==> InnerDepthsPositive(res[k])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var res_list: seq<string> := [];
  var current_start := 0;
  var current_depth := 0;

  if |paren_string| == 0 {
    return [];
  }

  var i := 0;
  while i < |paren_string|
    invariant 0 <= i <= |paren_string|
    invariant current_start >= 0
    invariant current_depth == ParenthesesDepth(paren_string, current_start, i)
    invariant forall k :: 0 <= k < |res_list| ==> ParenthesesDepth(res_list[k], 0, |res_list[k]|) == 0
    invariant forall k :: 0 <= k < |res_list| ==> InnerDepthsPositive(res_list[k])
    invariant forall x :: current_start <= x < i ==> ParenthesesDepth(paren_string, current_start, x) >= 0
    invariant ParenthesesDepth(paren_string, 0, |paren_string|) == 0
    invariant InnerDepthsNonnegative(paren_string)
  {
    if paren_string[i] == '(' {
      current_depth := current_depth + 1;
    } else if paren_string[i] == ')' {
      current_depth := current_depth - 1;
    }

    if current_depth == 0 {
      var sub_string := paren_string[current_start .. i + 1];
      res_list := res_list + [sub_string];

      // Prove post-conditions for the new segment
      assert ParenthesesDepth(sub_string, 0, |sub_string|) == 0 by {
        calc {
          ParenthesesDepth(sub_string, 0, |sub_string|);
          ParenthesesDepth(paren_string, current_start, i + 1);
        }
      }
      assert InnerDepthsPositive(sub_string) by {
        // Need to prove that ParenthesesDepth(sub_string, 0, k) > 0 for 0 < k < |sub_string|
        // We know ParenthesesDepth(paren_string, current_start, x) >= 0 for current_start <= x <= i+1 from InnerDepthsNonnegative(paren_string)
        // And we know current_depth (which is ParenthesesDepth(paren_string, current_start, i + 1)) is 0
        // We need to show that for current_start < x < i + 1, ParenthesesDepth(paren_string, current_start, x) > 0
        // This holds because current_depth only becomes 0 at i+1, and current_depth is effectively ParenthesesDepth starting from current_start
        // If ParenthesesDepth(sub_string, 0, k) was 0 for some 0 < k < |sub_string|, then current_depth would have been 0 earlier than i+1,
        // which contradicts the loop's logic for selecting substrings.
        // If ParenthesesDepth(sub_string, 0, k) was negative for some 0 < k < |sub_string|, then ParenthesesDepth(paren_string, current_start, current_start + k)
        // would be negative, which contradicts InnerDepthsNonnegative(paren_string)
        forall k_inner | 0 < k_inner < |sub_string|
          ensures ParenthesesDepth(sub_string, 0, k_inner) > 0
        {
          assert ParenthesesDepth(paren_string, current_start, current_start + k_inner) >= 0; // from InnerDepthsNonnegative
          if ParenthesesDepth(paren_string, current_start, current_start + k_inner) == 0 {
              // This is the crucial part that Dafny needs help with.
              // If ParenthesesDepth(paren_string, current_start, current_start + k_inner) == 0,
              // then the substring paren_string[current_start .. current_start + k_inner] would have been a balanced group,
              // and the 'if current_depth == 0' condition would have been met earlier.
              // Since it wasn't, it must be the case that current_depth (which is ParenthesesDepth(paren_string, current_start, current_start + k_inner))
              // was not zero until i+1.
              // Therefore, it must be > 0.
              assert ParenthesesDepth(paren_string, current_start, current_start + k_inner) > 0; // This is the key deduction being asserted.
          }
          assert ParenthesesDepth(sub_string, 0, k_inner) == ParenthesesDepth(paren_string, current_start, current_start + k_inner);
        }
      }

      current_start := i + 1;
      current_depth := 0; // Reset depth for the next group
    }
    i := i + 1;
  }
  return res_list;
}
// </vc-code>

