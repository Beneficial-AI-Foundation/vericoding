ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

// <vc-helpers>
function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  var s := if n == 0 then "" else Int2Str(n/2) + (if n%2==0 then "0" else "1");
  if s == "" then "0" else s
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  var x := Str2Int(sx);
  var y := Str2Int(sy);
  var z := Str2Int(sz);

  if y == 0 
  {
    calc {
      Exp_int(x, y) % z;
      Exp_int(x, 0) % z;
      1 % z;
    }
    assert Exp_int(x, y) % z == 1 % z;
    return Int2Str(1 % z);
  }
  else 
  {
    var res_int := x % z;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant res_int == Exp_int(x, Exp_int(2, i)) % z
    {
      calc {
        Exp_int(x, Exp_int(2, i+1)) % z;
        Exp_int(x, 2 * Exp_int(2, i)) % z;
        Exp_int(Exp_int(x, Exp_int(2, i)), 2) % z;
        (Exp_int(x, Exp_int(2, i)) * Exp_int(x, Exp_int(2, i))) % z;
        ( (Exp_int(x, Exp_int(2, i)) % z) * (Exp_int(x, Exp_int(2, i)) % z) ) % z;
        (res_int * res_int) % z;
      }
      res_int := (res_int * res_int) % z;
      i := i + 1;
    }
    calc {
      Exp_int(x, y) % z;
      Exp_int(x, Exp_int(2, n)) % z;
    }
    assert Exp_int(x, y) % z == Exp_int(x, Exp_int(2, n)) % z;
    assert Exp_int(x, y) % z == res_int;
    return Int2Str(res_int);
  }
}
// </vc-code>

