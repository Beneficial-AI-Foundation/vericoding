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

// <vc-helpers>
function reverse(s: string): string
  ensures |reverse(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverse(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 then ""
  else reverse(s[1..]) + [s[0]]
}

lemma reverse_concat(s: string, t: string)
  ensures reverse(s + t) == reverse(t) + reverse(s)
{
  if |s| == 0 {
    assert reverse("" + t) == reverse(t) == reverse(t) + "";
  } else if |t| == 0 {
    assert reverse(s + "") == reverse(s) == "" + reverse(s);
  } else {
    var s0 := [s[0]];
    var sRest := s[1..];
    calc {
      reverse(s + t);
      reverse(s0 + sRest + t);
      reverse(sRest + t) + s0;
      { reverse_concat(sRest, t); }
      (reverse(t) + reverse(sRest)) + s0;
      reverse(t) + (reverse(sRest) + s0);
      reverse(t) + reverse(s0 + sRest);
      reverse(t) + reverse(s);
    }
  }
}

lemma reverse_reverse(s: string)
  ensures reverse(reverse(s)) == s
{
  if |s| == 0 {
    assert reverse(reverse("")) == reverse("") == "";
  } else {
    var s0 := [s[0]];
    var sRest := s[1..];
    calc {
      reverse(reverse(s));
      reverse(reverse(s0 + sRest));
      reverse(reverse(sRest) + s0);
      { reverse_concat(reverse(sRest), s0); }
      reverse(s0) + reverse(reverse(sRest));
      { reverse_reverse(sRest); }
      reverse(s0) + sRest;
      s0 + sRest;
      s;
    }
  }
}

lemma reverse_length(s: string)
  ensures |reverse(s)| == |s|
{
  // This follows from the function definition's ensures clause
}
// </vc-helpers>

// <vc-spec>
method circular_shift(a: nat, shift: nat) returns (shifted: string)
  // post-conditions-start
  ensures |shifted| == |natToString(a)|
  ensures var s := natToString(a); shift > |s| ==> forall i :: 0 <= i < |s| ==> shifted[i] == s[|s| - 1 - i]
  ensures var s := natToString(a); shift <= |s| ==> shifted == s[|s| - shift..] + s[..|s| - shift]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var s := natToString(a);
  var n := |s|;
  
  if shift == 0 || n == 0 {
    shifted := s;
  } else if shift > n {
    shifted := reverse(s);
  } else {
    shifted := s[n - shift..] + s[..n - shift];
  }
}
// </vc-code>

method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
{
  assume{:axiom} false;
}