// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function PalindromeProp(x: seq<char>): bool { forall i :: 0 <= i < |x| ==> x[i] == x[|x| - 1 - i] }
// </vc-helpers>

// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
    ensures
        result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - 1 - i])
// </vc-spec>
// <vc-code>
{
  result := (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - 1 - i]);
}
// </vc-code>
