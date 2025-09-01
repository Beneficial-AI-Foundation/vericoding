function represents_byte(a: char) : bool
{
    a in "01"
}
function char_xor(a: char, b: char): char
    requires represents_byte(a)
    requires represents_byte(b)
{
    if (a == b) then
        '0'
    else
        '1'
}

// <vc-helpers>
lemma CharXorRep(a: char, b: char)
  requires represents_byte(a)
  requires represents_byte(b)
  ensures represents_byte(char_xor(a, b))
{
  if a == b {
    assert char_xor(a, b) == '0';
  } else {
    assert char_xor(a, b) == '1';
  }
}
// </vc-helpers>

// <vc-spec>
method string_xor(a: string, b: string) returns (result: string)
    // pre-conditions-start
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> represents_byte(a[i])
    requires forall i :: 0 <= i < |b| ==> represents_byte(b[i])
    // pre-conditions-end
    // post-conditions-start
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> represents_byte(result[i])
    ensures forall i :: 0 <= i < |result| ==> result[i] == char_xor(a[i], b[i])
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var res := ([] : seq<char>);
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == char_xor(a[j], b[j])
    invariant forall j :: 0 <= j < i ==> represents_byte(res[j])
  {
    var c := char_xor(a[i], b[i]);
    CharXorRep(a[i], b[i]);
    res := res + [c];
    i := i + 1;
  }
  result := res;
}
// </vc-code>

