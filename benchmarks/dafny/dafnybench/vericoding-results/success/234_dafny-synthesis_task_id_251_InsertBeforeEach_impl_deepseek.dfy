

// <vc-helpers>
lemma InsertBeforeEachLemma(s: seq<string>, x: string, i: int)
  requires 0 <= i <= |s|
  ensures |InsertBeforeEachAux(s, x, i)| == 2 * i
  ensures forall j :: 0 <= j < i ==> InsertBeforeEachAux(s, x, i)[2*j] == x && InsertBeforeEachAux(s, x, i)[2*j + 1] == s[j]
  decreases i
{
  if i > 0 {
    InsertBeforeEachLemma(s, x, i - 1);
  }
}

function InsertBeforeEachAux(s: seq<string>, x: string, i: int): seq<string>
  requires 0 <= i <= |s|
  ensures |InsertBeforeEachAux(s, x, i)| == 2 * i
  ensures forall j :: 0 <= j < i ==> InsertBeforeEachAux(s, x, i)[2*j] == x && InsertBeforeEachAux(s, x, i)[2*j + 1] == s[j]
  decreases i
{
  if i == 0 then []
  else InsertBeforeEachAux(s, x, i - 1) + [x] + [s[i - 1]]
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method InsertBeforeEach(s: seq<string>, x: string) returns (v: seq<string>)
        ensures |v| == 2 * |s|
        ensures forall i :: 0 <= i < |s| ==> v[2*i] == x && v[2*i + 1] == s[i]
// </vc-spec>
// <vc-code>
{
  v := InsertBeforeEachAux(s, x, |s|);
  InsertBeforeEachLemma(s, x, |s|);
}
// </vc-code>

