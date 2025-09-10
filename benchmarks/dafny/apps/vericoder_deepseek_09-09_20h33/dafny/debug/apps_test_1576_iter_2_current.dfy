predicate ValidInput(t: string)
{
    |t| >= 1
}

// <vc-helpers>
lemma ReverseReverseIdentity(s: seq<char>)
  ensures Reverse(Reverse(s)) == s
{
  if |s| == 0 {
  } else {
    ReverseReverseIdentity(s[1..]);
    assert Reverse(Reverse(s)) == Reverse(Reverse(s[1..]) + [s[0]]) == Reverse(Reverse(s[1..])) + [s[0]] == s[1..] + [s[0]] == s;
  }
}

function Reverse(s: seq<char>): seq<char> {
  if |s| == 0 then [] else Reverse(s[1..]) + [s[0]]
}

lemma ReverseLength(s: seq<char>)
  ensures |Reverse(s)| == |s|
{
  if |s| == 0 {
  } else {
    ReverseLength(s[1..]);
    assert |Reverse(s)| == |Reverse(s[1..]) + [s[0]]| == |Reverse(s[1..])| + 1 == |s[1..]| + 1 == (|s| - 1) + 1 == |s|;
  }
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
  result := "";
  var i := 0;
  while (i < |chars|)
    invariant |result| == i
    invariant i <= |chars|
  {
    result := [chars[i]] + result;
    i := i + 1;
  }
  ReverseLength(chars);
  assert |result| == |chars|;
}
// </vc-code>

