// <vc-preamble>
predicate IsLowerCase(c: char)
{
    'a' <= c && c <= 'z'
}

function ShiftMinus32(c: char): char
    requires 'a' <= c <= 'z'
{
    (c as int - 32) as char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): strengthen lemma about lowercase range and result of ShiftMinus32 */
lemma LowercaseIsRange(c: char)
  requires IsLowerCase(c)
  ensures 'a' <= c <= 'z'
  ensures 'A' <= ShiftMinus32(c) <= 'Z'
{
  assert 'a' <= c && c <= 'z';
  assert (ShiftMinus32(c) as int) == (c as int - 32);
  assert ('A' as int) <= (c as int - 32) <= ('Z' as int);
  assert 'A' <= ShiftMinus32(c) <= 'Z';
}

// </vc-helpers>

// <vc-spec>
method ToUppercase(s: string) returns (result: string)
    ensures
        |result| == |s|
    ensures
        forall i :: 0 <= i < |s| ==> 
            var c := s[i];
            var r := result[i];
            if IsLowerCase(c) then
                r == ShiftMinus32(c)
            else
                r == c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build char array and convert to string using array slice */
  var n := |s|;
  var arr := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant arr.Length == n
    invariant forall j :: 0 <= j < i ==> (if IsLowerCase(s[j]) then arr[j] == ShiftMinus32(s[j]) else arr[j] == s[j])
  {
    var c := s[i];
    if IsLowerCase(c) {
      LowercaseIsRange(c);
      arr[i] := ShiftMinus32(c);
    } else {
      arr[i] := c;
    }
    i := i + 1;
  }
  result := arr[..];
}

// </vc-code>
