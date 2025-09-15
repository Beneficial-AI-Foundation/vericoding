// <vc-preamble>
function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}

function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
// </vc-preamble>

// <vc-helpers>
function revIndex(k: int, n: int): int { n - 1 - k }
lemma RevIndexBounds(k: int, n: int)
  requires 0 <= k < n
  ensures 0 <= n - 1 - k < n
{ }
// </vc-helpers>

// <vc-spec>
method reverse(str: string) returns (rev: string)

    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
// </vc-spec>
// <vc-code>
{
  var r := "";
  var k := 0;
  while k < |str|
    invariant 0 <= k <= |str|
    invariant |r| == k
    invariant forall j :: 0 <= j < k ==> r[j] == str[|str| - 1 - j]
    decreases |str| - k
  {
    r := r + str[|str| - 1 - k .. |str| - k];
    k := k + 1;
  }
  rev := r;
}
// </vc-code>
