predicate ValidInput(t: string)
{
    |t| >= 1
}

// <vc-helpers>
predicate ValidInput(t: string)
{
    |t| >= 1
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
  }
}

lemma ReverseReverseIdentity(s: seq<char>)
  ensures Reverse(Reverse(s)) == s
{
  if |s| == 0 {
  } else {
    ReverseReverseIdentity(s[1..]);
    calc {
      Reverse(Reverse(s));
      ==
      Reverse(Reverse(s[1..]) + [s[0]]);
      == { ReverseAppend(Reverse(s[1..]), [s[0]]); }
      Reverse([s[0]]) + Reverse(Reverse(s[1..]));
      == { ReverseSingle(s[0]); ReverseReverseIdentity(s[1..]); }
      [s[0]] + s[1..];
      ==
      s;
    }
  }
}

lemma ReverseAppend(s1: seq<char>, s2: seq<char>)
  ensures Reverse(s1 + s2) == Reverse(s2) + Reverse(s1)
{
  if |s1| == 0 {
    assert Reverse([] + s2) == Reverse(s2) == Reverse(s2) + Reverse([]);
  } else {
    ReverseAppend(s1[1..], s2);
    assert Reverse(s1 + s2) == Reverse((s1[1..] + s2) + [s1[0]]) == Reverse(s1[1..] + s2) + [s1[0]] == (Reverse(s2) + Reverse(s1[1..])) + [s1[0]] == Reverse(s2) + (Reverse(s1[1..]) + [s1[0]]) == Reverse(s2) + Reverse(s1);
  }
}

lemma ReverseSingle(c: char)
  ensures Reverse([c]) == [c]
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
  result := "";
  var i := 0;
  while (i < |chars|)
    invariant |result| == i
    invariant i <= |chars|
    invariant result == Reverse(chars[0..i])
  {
    result := [chars[i]] + result;
    i := i + 1;
  }
  assert result == Reverse(chars[0..|chars|]) == Reverse(chars);
  ReverseReverseIdentity(chars);
  assert Reverse(result) == chars;
}
// </vc-code>

