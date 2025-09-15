// <vc-preamble>
function is_palindrome_pred(s : seq<int>) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method will_it_fly(s: seq<int>, w: int) returns (result: bool)

    requires |s| > 0

    ensures result <==> is_palindrome_pred(s) && sum(s) <= w
// </vc-spec>
// <vc-code>
{
  var is_pal := true;
  var i := 0;
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant is_pal <==> forall k :: 0 <= k < i ==> s[k] == s[|s| - 1 - k]
  {
    if s[i] != s[|s| - 1 - i] {
      is_pal := false;
      break;
    }
    i := i + 1;
  }
  var total := sum(s);
  result := is_pal && total <= w;
}
// </vc-code>
