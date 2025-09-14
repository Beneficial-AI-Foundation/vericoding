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

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Int2Str(n: nat): string
  decreases n
{
  if n == 0 then "0" else
  Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Int2StrSound(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
    calc {
      Str2Int(Int2Str(n));
      Str2Int("0");
      0;
    }
  } else {
    calc {
      Str2Int(Int2Str(n));
      Str2Int(Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0"));
      2 * Str2Int(Int2Str(n / 2)) + (if n % 2 == 1 then 1 else 0);
    }
    Int2StrSound(n / 2);
    calc {
      2 * Str2Int(Int2Str(n / 2)) + (if n % 2 == 1 then 1 else 0);
      2 * (n / 2) + (if n % 2 == 1 then 1 else 0);
      { assert n == 2 * (n / 2) + n % 2; }
      n;
    }
  }
}

function Reverse(s: string): string
  decreases |s|
{
  if |s| == 0 then s else Reverse(s[1..]) + [s[0]]
}

function AddBitStrings(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  decreases |s1|, |s2|
{
  if |s1| == 0 then s2
  else if |s2| == 0 then s1
  else
    var sum := (if s1[|s1|-1] == '1' then 1 else 0) + (if s2[|s2|-1] == '1' then 1 else 0);
    var tail := AddBitStrings(s1[0..|s1|-1], s2[0..|s2|-1]);
    var carry_bit := if sum >= 2 then "1" else "0";
    var sum_bit := if sum % 2 == 1 then "1" else "0";
    // Add the carry to the tail.
    var new_tail := if carry_bit == "1" then AddBitStrings(tail, "1") else tail;
    new_tail + sum_bit
}

lemma AddSound(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(AddBitStrings(s1, s2))
  ensures Str2Int(AddBitStrings(s1, s2)) == Str2Int(s1) + Str2Int(s2)
  decreases |s1|, |s2|
{
  if |s1| == 0 {
    calc {
      Str2Int(AddBitStrings(s1, s2));
      Str2Int(s2);
      0 + Str2Int(s2);
      Str2Int(s1) + Str2Int(s2);
    }
  } else if |s2| == 0 {
    calc {
      Str2Int(AddBitStrings(s1, s2));
      Str2Int(s1);
      Str2Int(s1) + 0;
      Str2Int(s1) + Str2Int(s2);
    }
  } else {
    var sum := (if s1[|s1|-1] == '1' then 1 else 0) + (if s2[|s2|-1] == '1' then 1 else 0);
    var tail := AddBitStrings(s1[0..|s1|-1], s2[0..|s2|-1]);
    var carry_bit := if sum >= 2 then "1" else "0";
    var sum_bit := if sum % 2 == 1 then "1" else "0";
    var new_tail := if carry_bit == "1" then AddBitStrings(tail, "1") else tail;
    
    AddSound(s1[0..|s1|-1], s2[0..|s2|-1]);
    
    calc {
      Str2Int(AddBitStrings(s1, s2));
      Str2Int(new_tail + sum_bit);
      2 * Str2Int(new_tail) + (if sum_bit == "1" then 1 else 0);
    }
    
    if carry_bit == "1" {
      calc {
        2 * Str2Int(new_tail) + (if sum_bit == "1" then 1 else 0);
        2 * (Str2Int(tail) + 1) + (if sum_bit == "1" then 1 else 0);
        2 * Str2Int(tail) + 2 + (if sum_bit == "1" then 1 else 0);
      }
    } else {
      calc {
        2 * Str2Int(new_tail) + (if sum_bit == "1" then 1 else 0);
        2 * Str2Int(tail) + (if sum_bit == "1" then 1 else 0);
      }
    }
    
    calc {
      Str2Int(s1) + Str2Int(s2);
      (2 * Str2Int(s1[0..|s1|-1]) + (if s1[|s1|-1] == '1' then 1 else 0)) +
        (2 * Str2Int(s2[0..|s2|-1]) + (if s2[|s2|-1] == '1' then 1 else 0));
      2 * (Str2Int(s1[0..|s1|-1]) + Str2Int(s2[0..|s2|-1])) + 
        ((if s1[|s1|-1] == '1' then 1 else 0) + (if s2[|s2|-1] == '1' then 1 else 0));
      2 * Str2Int(tail) + sum;
    }
  }
}

function SubBitStrings(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  decreases |s1|
{
  if |s2| == 0 then s1
  else if |s1| == 0 then ""  // This case only happens if s2 is also 0
  else
    var b1 := if s1[|s1|-1] == '1' then 1 else 0;
    var b2 := if s2[|s2|-1] == '1' then 1 else 0;
    var borrow := if b1 < b2 then 1 else 0;
    var tail := if borrow == 1 
                then SubBitStrings(s1[0..|s1|-1], AddBitStrings(s2[0..|s2|-1], "1"))
                else SubBitStrings(s1[0..|s1|-1], s2[0..|s2|-1]);
    var diff_bit := if (b1 - b2 + borrow * 2) % 2 == 1 then "1" else "0";
    tail + diff_bit
}

lemma SubSound(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(SubBitStrings(s1, s2))
  ensures Str2Int(SubBitStrings(s1, s2)) == Str2Int(s1) - Str2Int(s2)
  decreases |s1|
{
  if |s2| == 0 {
    calc {
      Str2Int(SubBitStrings(s1, s2));
      Str2Int(s1);
      Str2Int(s1) - 0;
      Str2Int(s1) - Str2Int(s2);
    }
  } else if |s1| == 0 {
    // This case only happens when both strings are empty
    calc {
      Str2Int(SubBitStrings(s1, s2));
      Str2Int("");
      0;
      0 - 0;
      Str2Int(s1) - Str2Int(s2);
    }
  } else {
    var b1 := if s1[|s1|-1] == '1' then 1 else 0;
    var b2 := if s2[|s2|-1] == '1' then 1 else 0;
    var borrow := if b1 < b2 then 1 else 0;
    
    if borrow == 1 {
      SubSound(s1[0..|s1|-1], AddBitStrings(s2[0..|s2|-1], "1"));
      AddSound(s2[0..|s2|-1], "1");
      
      calc {
        Str2Int(s1) - Str2Int(s2);
        (2 * Str2Int(s1[0..|s1|-1]) + b1) - (2 * Str2Int(s2[0..|s2|-1]) + b2);
        2 * (Str2Int(s1[0..|s1|-1]) - Str2Int(s2[0..|s2|-1])) + (b1 - b2);
        2 * (Str2Int(s1[0..|s1|-1]) - (Str2Int(s2[0..|s2|-1]) + 1)) + (b1 - b2 + 2);
        2 * Str2Int(SubBitStrings(s1[0..|s1|-1], AddBitStrings(s2[0..|s2|-1], "1"))) + 
          ((b1 - b2 + 2) % 2);
      }
    } else {
      SubSound(s1[0..|s1|-1], s2[0..|s2|-1]);
      
      calc {
        Str2Int(s1) - Str2Int(s2);
        (2 * Str2Int(s1[0..|s1|-1]) + b1) - (2 * Str2Int(s2[0..|s2|-1]) + b2);
        2 * (Str2Int(s1[0..|s1|-1]) - Str2Int(s2[0..|s2|-1])) + (b1 - b2);
        2 * Str2Int(SubBitStrings(s1[0..|s1|-1], s2[0..|s2|-1])) + ((b1 - b2) % 2);
      }
    }
  }
}

lemma MidProperty(dividend: string, divisor: string, mid: nat)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  requires 0 < mid < Str2Int(dividend)
  ensures Str2Int(dividend) == 2 * mid + (if Str2Int(dividend) % 2 == 1 then 1 else 0)
{
  calc {
    Str2Int(dividend);
    2 * mid + (Str2Int(dividend) - 2 * mid);
    2 * mid + (if Str2Int(dividend) - 2 * mid == 1 then 1 else 0);
    {
      assert Str2Int(dividend) == 2 * mid + (Str2Int(dividend) % 2);
      assert Str2Int(dividend) - 2 * mid == Str2Int(dividend) % 2;
    }
    2 * mid + (if Str2Int(dividend) % 2 == 1 then 1 else 0);
  }
}

lemma DivModRecurrence(dividend: string, divisor: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  requires Str2Int(dividend) >= Str2Int(divisor)
  ensures Str2Int(dividend) == Str2Int(divisor) * (Str2Int(dividend) / Str2Int(divisor)) + Str2Int(dividend) % Str2Int(divisor)
{
  var q := Str2Int(dividend) / Str2Int(divisor);
  var r := Str2Int(dividend) % Str2Int(divisor);
  calc {
    Str2Int(dividend);
    Str2Int(divisor) * q + r;
  }
}
// </vc-helpers>

// <vc-spec>
method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
// </vc-spec>
// <vc-code>
{
  if Str2Int(dividend) < Str2Int(divisor) {
    quotient := "0";
    remainder := dividend;
  } else {
    var mid := Str2Int(dividend) / 2;
    var midStr := Int2Str(mid);
    var q, r := DivMod(midStr, divisor);
    var doubled := AddBitStrings(AddBitStrings(midStr, midStr), r);
    
    if Str2Int(dividend) % 2 == 1 {
      doubled := AddBitStrings(doubled, "1");
    }
    
    MidProperty(dividend, divisor, mid);
    assert Str2Int(doubled) == Str2Int(dividend);
    
    if Str2Int(doubled) >= Str2Int(divisor) {
      quotient := AddBitStrings(q, "1");
      remainder := SubBitStrings(doubled, divisor);
    } else {
      quotient := q;
      remainder := doubled;
    }
    
    DivModRecurrence(doubled, divisor);
  }
}
// </vc-code>

