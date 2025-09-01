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
function reverse_func(s: string): string
  ensures |reverse_func(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverse_func(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 then ""
  else reverse_func(s[1..]) + [s[0]]
}

lemma reverse_concat(s: string, t: string)
  ensures reverse_func(s + t) == reverse_func(t) + reverse_func(s)
{
  if |s| == 0 {
    assert reverse_func("" + t) == reverse_func(t) == reverse_func(t) + "";
  } else if |t| == 0 {
    assert reverse_func(s + "") == reverse_func(s) == "" + reverse_func(s);
  } else {
    var s0 := [s[0]];
    var sRest := s[1..];
    calc {
      reverse_func(s + t);
      reverse_func(s0 + sRest + t);
      reverse_func(sRest + t) + s0;
      { reverse_concat(sRest, t); }
      (reverse_func(t) + reverse_func(sRest)) + s0;
      reverse_func(t) + (reverse_func(sRest) + s0);
      reverse_func(t) + reverse_func(s0 + sRest);
      reverse_func(t) + reverse_func(s);
    }
  }
}

lemma reverse_reverse(s: string)
  ensures reverse_func(reverse_func(s)) == s
{
  if |s| == 0 {
    assert reverse_func(reverse_func("")) == reverse_func("") == "";
  } else {
    var s0 := [s[0]];
    var sRest := s[1..];
    calc {
      reverse_func(reverse_func(s));
      reverse_func(reverse_func(s0 + sRest));
      reverse_func(reverse_func(sRest) + s0);
      { reverse_concat(reverse_func(sRest), s0); }
      reverse_func(s0) + reverse_func(reverse_func(sRest));
      { reverse_reverse(sRest); }
      reverse_func(s0) + sRest;
      s0 + sRest;
      s;
    }
  }
}

lemma reverse_length(s: string)
  ensures |reverse_func(s)| == |s|
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
    shifted := reverse_func(s);
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