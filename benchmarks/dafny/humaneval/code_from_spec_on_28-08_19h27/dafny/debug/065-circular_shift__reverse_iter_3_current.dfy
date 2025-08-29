type stringNat = s: string |
  |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
  forall i | 0 <= i < |s| :: s[i] in "0123456789"
  witness "1"
function natToString(n: nat): stringNat {
  match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => natToString(n / 10) + natToString(n % 10)
}
method circular_shift(a: nat, shift: nat) returns (shifted: string)
  // post-conditions-start
  ensures |shifted| == |natToString(a)|
  ensures var s := natToString(a); shift > |s| ==> forall i :: 0 <= i < |s| ==> shifted[i] == s[|s| - 1 - i]
  ensures var s := natToString(a); shift <= |s| ==> shifted == s[|s| - shift..] + s[..|s| - shift]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma reverseLength(s: string)
  ensures |s| == 0 ==> |""| == |s|
  ensures |s| == 1 ==> |s| == |s|
  ensures |s| > 1 ==> |reverseHelper(s[1..]) + [s[0]]| == |s|
{
  if |s| <= 1 {
  } else {
    reverseLength(s[1..]);
  }
}

lemma reverseCharAt(s: string, i: int)
  requires 0 <= i < |s|
  requires |s| > 1
  ensures var tail_rev := reverseHelper(s[1..]); 
          var result := tail_rev + [s[0]];
          result[i] == s[|s| - 1 - i]
{
  var tail_rev := reverseHelper(s[1..]);
  var result := tail_rev + [s[0]];
  
  assert |result| == |s|;
  assert |tail_rev| == |s| - 1;
  
  if i == |s| - 1 {
    assert i < |result|;
    assert result[i] == result[|result| - 1] == s[0];
    assert s[|s| - 1 - i] == s[0];
  } else {
    assert i < |s| - 1;
    assert i < |tail_rev|;
    assert result[i] == tail_rev[i];
    reverseCharAtHelper(s[1..], i);
    assert tail_rev[i] == s[1..][|s[1..]| - 1 - i];
    assert s[1..][|s[1..]| - 1 - i] == s[|s| - 1 - i];
  }
}

lemma reverseCharAtHelper(s: string, i: int)
  requires 0 <= i < |s|
  ensures |s| > 0
  ensures reverseHelper(s)[i] == s[|s| - 1 - i]
{
  if |s| <= 1 {
    assert reverseHelper(s) == s;
  } else {
    assert |s| > 1;
    var result := reverseHelper(s[1..]) + [s[0]];
    assert reverseHelper(s) == result;
    assert |result| == |s|;
    if i == |s| - 1 {
      assert result[i] == s[0];
      assert s[|s| - 1 - i] == s[0];
    } else {
      assert i < |s| - 1;
      assert i < |reverseHelper(s[1..])|;
      reverseCharAtHelper(s[1..], i);
    }
  }
}

function reverseHelper(s: string): string
{
  if |s| == 0 then ""
  else if |s| == 1 then s
  else reverseHelper(s[1..]) + [s[0]]
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method reverse(str: string) returns (rev: string)
Reverse order. Ensures: returns the correct size/count; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method reverse(str: string) returns (rev: string)
  ensures |rev| == |str|
  ensures forall i :: 0 <= i < |str| ==> rev[i] == str[|str| - 1 - i]
// </vc-spec>
// <vc-code>
{
  if |str| == 0 {
    rev := "";
  } else if |str| == 1 {
    rev := str;
  } else {
    var tail_rev := reverse(str[1..]);
    rev := tail_rev + [str[0]];
    
    forall i | 0 <= i < |str|
      ensures rev[i] == str[|str| - 1 - i]
    {
      reverseCharAtHelper(str, i);
    }
  }
}
// </vc-code>
