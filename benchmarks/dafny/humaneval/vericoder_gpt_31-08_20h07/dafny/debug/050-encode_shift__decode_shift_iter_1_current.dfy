function encode_char(c: char): char
  // pre-conditions-start
  requires 'a' <= c <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures 'a' <= encode_char(c) <= 'z'
  // post-conditions-end
{
  // impl-start
  ((c as int - 'a' as int + 5) % 26 + 'a' as int) as char
  // impl-end
}
function decode_char(c: char): char
  // pre-conditions-start
  requires 'a' <= c <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures 'a' <= decode_char(c) <= 'z'
  ensures encode_char(decode_char(c)) == c
  // post-conditions-end
{
  // impl-start
  ((c as int - 'a' as int - 5) % 26 + 'a' as int) as char
  // impl-end
}
method encode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == encode_char(s[i])
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma IndexOfAppend<T>(xs: seq<T>, x: T, j: int)
  ensures 0 <= j < |xs| ==> (xs + [x])[j] == xs[j]
  ensures (xs + [x])[|xs|] == x
{}
// </vc-helpers>

// <vc-spec>
method decode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == decode_char(s[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var u: string := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |u| == i
    invariant forall j :: 0 <= j < i ==> u[j] == decode_char(s[j])
  {
    assert 0 <= i < |s|;
    assert 'a' <= s[i] <= 'z';

    var u0 := u;
    assert |u0| == i;
    assert forall j :: 0 <= j < i ==> u0[j] == decode_char(s[j]);

    var ch := decode_char(s[i]);
    u := u0 + [ch];
    i := i + 1;

    assert |u| == |u0| + 1;
    assert |u0| == i - 1;

    assert forall j :: 0 <= j < i ==> u[j] == decode_char(s[j]) {
      IndexOfAppend(u0, ch, j);
      if j < i - 1 {
        assert j < |u0|;
        assert u[j] == u0[j];
        assert u0[j] == decode_char(s[j]);
      } else {
        assert j == i - 1;
        assert j == |u0|;
        assert u[j] == ch;
      }
    }
  }
  t := u;
}
// </vc-code>

