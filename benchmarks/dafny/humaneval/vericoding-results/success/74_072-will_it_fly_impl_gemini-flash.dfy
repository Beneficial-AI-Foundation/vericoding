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
  var s_is_palindrome := is_palindrome_pred(s);
  var s_sum := sum(s);
  result := s_is_palindrome && s_sum <= w;
}
// </vc-code>
