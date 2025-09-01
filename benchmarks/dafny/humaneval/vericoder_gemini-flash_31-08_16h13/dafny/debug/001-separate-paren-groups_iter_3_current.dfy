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
  ensures ParenthesesDepth(s, 0, |s|) == 0 && (forall i :: 0 < i < |s| ==> ParenthesesDepth(s, 0, i) > 0)
{
  ParenthesesDepth(s, 0, |s|) == 0 && (forall i :: 0 < i < |s| ==> ParenthesesDepth(s, 0, i) > 0)
}

function InvariantHolds(paren_string: string, current_start: int, i: int, current_depth: int, res_list: seq<string>) : bool
{
  0 <= i <= |paren_string|
  && 0 <= current_start <= i
  && current_depth == ParenthesesDepth(paren_string, current_start, i)
  && (forall k :: 0 <= k < |res_list| ==> ParenthesesDepth(res_list[k], 0, |res_list[k]|) == 0)
  && (forall k :: 0 <= k < |res_list| ==> is_balanced_and_positive(res_list[k]))
  && (forall x :: current_start < x <= i ==> ParenthesesDepth(paren_string, current_start, x) >= 0)
  && ParenthesesDepth(paren_string, 0, |paren_string|) == 0
  && InnerDepthsNonnegative(paren_string)
  && (forall x :: current_start < x < i ==> ParenthesesDepth(paren_string, current_start, x) > 0)
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
    invariant InvariantHolds(paren_string, current_start, i, current_depth, res_list)
    invariant ParenthesesDepth(paren_string, 0, current_start) == 0
  {
    var new_depth := current_depth;
    if paren_string[i] == '(' {
      new_depth := current_depth + 1;
    } else if paren_string[i] == ')' {
      new_depth := current_depth - 1;
    }
    current_depth := new_depth;

    if current_depth == 0 {
      var sub_string := paren_string[current_start .. i + 1];
      res_list := res_list + [sub_string];

      assert ParenthesesDepth(sub_string, 0, |sub_string|) == 0 by {
        calc {
          ParenthesesDepth(sub_string, 0, |sub_string|);
          ParenthesesDepth(paren_string, current_start, i + 1);
        }
        assert ParenthesesDepth(paren_string, current_start, i + 1) == new_depth;
        assert new_depth == 0;
      }
      assert is_balanced_and_positive(sub_string) by {
        forall k_inner | 0 < k_inner < |sub_string|
          ensures ParenthesesDepth(sub_string, 0, k_inner) > 0
        {
          assert (current_start + k_inner) <= (i + 1);
          assert ParenthesesDepth(paren_string, 0, current_start + k_inner) >= 0; // From InnerDepthsNonnegative
          assert ParenthesesDepth(paren_string, current_start, current_start + k_inner) == ParenthesesDepth(paren_string, 0, current_start + k_inner) - ParenthesesDepth(paren_string, 0, current_start);
          assert ParenthesesDepth(paren_string, current_start, current_start) == 0; // i.e. ParenthesesDepth(paren_string, 0, current_start) - ParenthesesDepth(paren_string, 0, current_start) == 0
          if current_start < current_start + k_inner < i + 1 {
            assert ParenthesesDepth(paren_string, current_start, current_start + k_inner) > 0;
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

