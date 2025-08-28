method circular_shift(a: nat, shift: nat) returns (shifted: string)
  // post-conditions-start
  ensures |shifted| == |natToString(a)|
  ensures var s := natToString(a); shift > |s| ==> forall i :: 0 <= i < |s| ==> shifted[i] == s[|s| - 1 - i]
  ensures var s := natToString(a); shift <= |s| ==> shifted == s[|s| - shift..] + s[..|s| - shift]
  // post-conditions-end
{
  // impl-start
  var s := natToString(a);
  if shift > |s| {
    s := reverse(s);
    return s;
  }

  shifted := "";
  var i := 0;
  var start := |s| - shift;
  while i < shift
    // invariants-start
    invariant 0 <= i <= shift
    invariant shifted == s[|s| - shift..][..i]
    // invariants-end
  {
    shifted := shifted + [s[start + i]];
    i := i + 1;
  }
  var added := "";
  i := 0;
  while i < |s| - shift
    // invariants-start
    invariant 0 <= i <= |s| - shift
    invariant added == s[..|s| - shift][..i]
    // invariants-end
  {
    added := added + [s[i]];
    i := i + 1;
  }
  assert shifted == s[|s| - shift..]; // assert-line
  assert added == s[..|s| - shift]; // assert-line
  shifted := shifted + added;
  // impl-end
}

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
// pure-end
function stringToNat(s: stringNat): nat
  decreases |s|
{
  if |s| == 1 then
      match s[0]
      case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
      case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
  else
      stringToNat(s[..|s|-1])*10 + stringToNat(s[|s|-1..|s|])
}
// pure-end
lemma natToStringThenStringToNatIdem(n: nat)
  ensures stringToNat(natToString(n)) == n
{
}
// pure-end
method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
{
    // impl-start
    rev := "";
    var i := 0;
    while (i < |str|)
        // invariants-start
        invariant i >= 0 && i <= |str|
        invariant |rev| == i
        invariant forall k :: 0 <= k < i ==> rev[k] == str[|str| - 1 - k]
        // invariants-end
    {
        rev := rev + [str[|str| - i - 1]];
        i := i + 1;
    }
    // impl-end
}
