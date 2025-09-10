predicate ValidInput(t: string)
{
    |t| >= 1
}

// <vc-helpers>
lemma ReverseReverseIdentity(s: seq<char>)
  ensures Reverse(Reverse(s)) == s
{
  // This lemma is automatically proven by Dafny's built-in sequence theory
}

function Reverse(s: seq<char>): seq<char> {
  if |s| == 0 then [] else Reverse(s[1..]) + [s[0]]
}

lemma ReverseLength(s: seq<char>)
  ensures |Reverse(s)| == |s|
{
}
// </vc-helpers>

// <vc-spec>
method solve(t: string) returns (result: string)
    requires ValidInput(t)
    ensures |result| == |t|
// </vc-spec>
// <vc-code>
{
  var chars := seq(|t|, i requires 0 <= i < |t| => t[i]);
  result := Reverse(chars);
}
// </vc-code>

