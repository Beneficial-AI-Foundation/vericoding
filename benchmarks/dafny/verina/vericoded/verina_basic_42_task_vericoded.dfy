// <vc-preamble>
predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed CountDigitsAppend lemma to correctly prove the postcondition */
function CountDigitsInString(s: string): nat
{
  if |s| == 0 then 0
  else (if IsDigit(s[0]) then 1 else 0) + CountDigitsInString(s[1..])
}

lemma CountDigitsAppend(s: string, i: nat)
  requires i < |s|
  ensures CountDigitsInString(s[..i+1]) == CountDigitsInString(s[..i]) + (if IsDigit(s[i]) then 1 else 0)
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
    assert CountDigitsInString(s[..0]) == 0;
    assert CountDigitsInString(s[..1]) == CountDigitsInString([s[0]]);
    assert CountDigitsInString([s[0]]) == (if IsDigit(s[0]) then 1 else 0);
  } else {
    assert s[..i+1][0] == s[0];
    assert s[..i+1][1..] == s[1..i+1];
    assert s[1..i+1] == s[1..][..i];
    assert s[..i][0] == s[0];
    assert s[..i][1..] == s[1..i];
    assert s[1..i] == s[1..][..i-1];
    
    calc == {
      CountDigitsInString(s[..i+1]);
      (if IsDigit(s[0]) then 1 else 0) + CountDigitsInString(s[1..i+1]);
      (if IsDigit(s[0]) then 1 else 0) + CountDigitsInString(s[1..][..i]);
    }
    
    calc == {
      CountDigitsInString(s[..i]);
      (if IsDigit(s[0]) then 1 else 0) + CountDigitsInString(s[1..i]);
      (if IsDigit(s[0]) then 1 else 0) + CountDigitsInString(s[1..][..i-1]);
    }
    
    CountDigitsAppend(s[1..], i-1);
  }
}
// </vc-helpers>

// <vc-spec>
method CountDigits(s: string) returns (result: nat)
    ensures result >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Implementation using helper function and lemma */
{
  result := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result == CountDigitsInString(s[..i])
  {
    CountDigitsAppend(s, i);
    if IsDigit(s[i]) {
      result := result + 1;
    }
    i := i + 1;
  }
  assert s[..|s|] == s;
}
// </vc-code>
