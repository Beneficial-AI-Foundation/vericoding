ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

function {:opaque} NthBit(s: string, i: nat): char
  requires ValidBitString(s)
  requires i < |s|
  ensures NthBit(s, i) == s[i]
  ensures NthBit(s, i) == '0' || NthBit(s, i) == '1'
{
  s[i]
}

lemma LemmaStr2IntProperties(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) < (1 << |s|)
  ensures |s| > 0 ==> (1 << (|s| - 1)) <= Str2Int(s) + 1
{
  if |s| == 0 {
    calc {
      Str2Int(s);
      0;
      1 << 0;
    }
    calc {
      (1 << (|s| - 1));
      (1 << -1);
    }
  } else {
    LemmaStr2IntProperties(s[0..|s|-1]);
    calc {
      Str2Int(s);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      2 * Str2Int(s[0..|s|-1]) + (if NthBit(s, |s|-1) == '1' then 1 else 0);
      <=
      2 * ((1 << (|s|-1)) - 1) + 1;
      ==
      (1 << |s|) - 2 + 1;
      <
      1 << |s|;
    }
    if |s| > 1 {
      calc {
        (1 << (|s| - 1));
        <=
        2 * Str2Int(s[0..|s|-1]) + 2;
        ==
        (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)) + (if s[|s|-1] == '0' then 2 else 1);
        ==
        Str2Int(s) + (if s[|s|-1] == '0' then 2 else 1);
      }
    }
  }
}

lemma LemmaSubtractionHelper(i: nat, j: nat, borrow: bool)
  requires i >= j + (if borrow then 1 else 0)
  ensures var new_borrow := j + (if borrow then 1 else 0) > i;
      var diff := (i + (1 << 1)) - (j + (if borrow then 1 else 0));
      diff < (1 << 1)
{
}
// </vc-helpers>

// <vc-spec>
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  var res := "";
  var borrow := false;
  var len := |s1|;
  
  if |s2| > len {
    len := |s2|;
  }
  
  for i := 0 to len
    invariant 0 <= i <= len
    invariant ValidBitString(res)
    invariant Str2Int(res) + (if borrow then Str2Int(s1[0..i]) else Str2Int(s1[0..i])) == Str2Int(s2[0..i]) + (if borrow then 1 else 0) * Str2Int(res)
  {
    var bit1 := if i < |s1| then s1[i] else '0';
    var bit2 := if i < |s2| then s2[i] else '0';
    var val1 := if bit1 == '1' then 1 else 0;
    var val2 := if bit2 == '1' then 1 else 0;
    
    var diff := val1 - val2 - (if borrow then 1 else 0);
    var new_borrow := diff < 0;
    var result_bit := if diff < 0 then diff + 2 else diff;
    
    res := res + (if result_bit == 1 then '1' else '0');
    borrow := new_borrow;
  }
  
  return NormalizeBitString(res);
}
// </vc-code>

