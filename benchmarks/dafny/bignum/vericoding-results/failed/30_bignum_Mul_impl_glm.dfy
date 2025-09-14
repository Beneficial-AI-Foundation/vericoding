ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

// <vc-helpers>
function {:opaque} Add(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(Add(s1, s2))
  ensures Str2Int(Add(s1, s2)) == Str2Int(s1) + Str2Int(s2)
{
  if |s1| == 0 then s2
  else if |s2| == 0 then s1
  else
    var last1 := s1[|s1|-1];
    var last2 := s2[|s2|-1];
    var s_first := if |s1| == 1 then "" else s1[0..|s1|-1];
    var s_second := if |s2| == 1 then "" else s2[0..|s2|-1];
    var sum_rest := Add(s_first, s_second);
    var carry := (last1 == '1' && last2 == '1') || (last1 == '1' && sum_rest != "" && sum_rest[|sum_rest|-1] == '1') || (last2 == '1' && sum_rest != "" && sum_rest[|sum_rest|-1] == '1');
    var least := if last1 == '1' then (if last2 == '1' then '0' else '1') else (if last2 == '1' then '1' else '0');
    if carry then Add(sum_rest, "1") + least.toString() else sum_rest + least.toString()
}

lemma {:fuel FixAddLemma,0} lemma_Add_zero(s: string)
  requires ValidBitString(s)
  ensures Add(s, "0") == s && Add("0", s) == s
{
  if |s| == 0 {
    calc {
      Add(s, "0");
      "0";
      s;
    }
  } else {
    calc {
      Add("0", s);
      { assert s[0..|s|-1] == "";
        assert Add("", s[0..|s|-1]) == s[0..|s|-1];
      }
      Add(s[0..|s|-1], "") + (if '0' == '1' then (if s[|s|-1] == '1' then '0' else '1') else s[|s|-1]).toString();
      s[0..|s|-1] + s[|s|-1].toString();
      s;
    }
    calc {
      Add(s, "0");
      { assert s[0..|s|-1] == "";
        assert Add(s[0..|s|-1], "") == s[0..|s|-1];
      }
      Add(s[0..|s|-1], "") + (if s[|s|-1] == '1' then (if '0' == '1' then '0' else '1') else '0').toString();
      s[0..|s|-1] + (if s[|s|-1] == '1' then '1' else '0').toString();
      s[0..|s|-1] + s[|s|-1].toString();
      s;
    }
  }
}

lemma {:fuel FixAddLemma,0} lemma_Add_associative(s1: string, s2: string, s3: string)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(s3)
  ensures Add(Add(s1, s2), s3) == Add(s1, Add(s2, s3))
{
  if |s1| == 0 {
    calc {
      Add(Add(s1, s2), s3);
      Add(s2, s3);
      Add(s1, Add(s2, s3));
    }
  } else if |s2| == 0 {
    calc {
      Add(Add(s1, s2), s3);
      Add(s1, s3);
      Add(s1, Add(s2, s3));
    }
  } else if |s3| == 0 {
    calc {
      Add(Add(s1, s2), s3);
      Add(s1, s2);
      Add(s1, Add(s2, s3));
    }
  } else {
    var last1 := s1[|s1|-1];
    var last2 := s2[|s2|-1];
    var last3 := s3[|s3|-1];
    var s_first1 := if |s1| == 1 then "" else s1[0..|s1|-1];
    var s_first2 := if |s2| == 1 then "" else s2[0..|s2|-1];
    var s_first3 := if |s3| == 1 then "" else s3[0..|s3|-1];
    
    lemma_Add_associative(s_first1, s_first2, s_first3);
    lemma_Add_associative(s_first1, s_first2, "1");
    lemma_Add_associative(Add(s_first1, s_first2), s_first3, "1");
    lemma_Add_associative(s_first1, Add(s_first2, s_first3), "1");
    
    var sum12 := Add(s_first1, s_first2);
    var sum23 := Add(s_first2, s_first3);
    var sum_rest123 := Add(Add(s_first1, s_first2), s_first3);
    var sum_rest132 := Add(s_first1, Add(s_first2, s_first3));
    
    calc {
      Add(Add(s1, s2), s3);
      Add(sum_rest123 + (if last1 == '1' then (if last2 == '1' then '0' else '1') else (if last2 == '1' then '1' else '0')).toString(), s3);
      { assert Add(sum_rest123, s_first3) == sum_rest123; }
      Add(sum_rest123 + (if last1 == '1' then (if last2 == '1' then '0' else '1') else (if last2 == '1' then '1' else '0')).toString(), s3);
      s1;
    }
  }
}

function {:fuel ShiftLeft,0} ShiftLeft(s: string, n: nat): string
  requires ValidBitString(s)
  ensures ValidBitString(ShiftLeft(s, n))
  ensures Str2Int(ShiftLeft(s, n)) == Str2Int(s) * (2^n)
{
  if n == 0 then s else ShiftLeft(s + "0", n - 1)
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  if |s1| == 0 || |s2| == 0 then
    "0"
  else if s2 == "1" then
    s1
  else
    var half := |s2| / 2;
    var s2_low := s2[0..half];
    var s2_high := s2[half..];
    var low_prod := Mul(s1, s2_low);
    var high_prod := Mul(s1, s2_high);
    var high_shifted := ShiftLeft(high_prod, |s2| - half);
    Add(high_shifted, low_prod)
}
// </vc-code>

