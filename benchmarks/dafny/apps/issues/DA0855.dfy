// <vc-preamble>
predicate ValidInput(n: int)
{
  0 <= n < 0x100000000
}

function ReverseBits32Spec(x: bv32): bv32
{
  var b0 := if (x & 0x00000001) != 0 then 0x80000000 else 0;
  var b1 := if (x & 0x00000002) != 0 then 0x40000000 else 0;
  var b2 := if (x & 0x00000004) != 0 then 0x20000000 else 0;
  var b3 := if (x & 0x00000008) != 0 then 0x10000000 else 0;
  var b4 := if (x & 0x00000010) != 0 then 0x08000000 else 0;
  var b5 := if (x & 0x00000020) != 0 then 0x04000000 else 0;
  var b6 := if (x & 0x00000040) != 0 then 0x02000000 else 0;
  var b7 := if (x & 0x00000080) != 0 then 0x01000000 else 0;
  var b8 := if (x & 0x00000100) != 0 then 0x00800000 else 0;
  var b9 := if (x & 0x00000200) != 0 then 0x00400000 else 0;
  var b10 := if (x & 0x00000400) != 0 then 0x00200000 else 0;
  var b11 := if (x & 0x00000800) != 0 then 0x00100000 else 0;
  var b12 := if (x & 0x00001000) != 0 then 0x00080000 else 0;
  var b13 := if (x & 0x00002000) != 0 then 0x00040000 else 0;
  var b14 := if (x & 0x00004000) != 0 then 0x00020000 else 0;
  var b15 := if (x & 0x00008000) != 0 then 0x00010000 else 0;
  var b16 := if (x & 0x00010000) != 0 then 0x00008000 else 0;
  var b17 := if (x & 0x00020000) != 0 then 0x00004000 else 0;
  var b18 := if (x & 0x00040000) != 0 then 0x00002000 else 0;
  var b19 := if (x & 0x00080000) != 0 then 0x00001000 else 0;
  var b20 := if (x & 0x00100000) != 0 then 0x00000800 else 0;
  var b21 := if (x & 0x00200000) != 0 then 0x00000400 else 0;
  var b22 := if (x & 0x00400000) != 0 then 0x00000200 else 0;
  var b23 := if (x & 0x00800000) != 0 then 0x00000100 else 0;
  var b24 := if (x & 0x01000000) != 0 then 0x00000080 else 0;
  var b25 := if (x & 0x02000000) != 0 then 0x00000040 else 0;
  var b26 := if (x & 0x04000000) != 0 then 0x00000020 else 0;
  var b27 := if (x & 0x08000000) != 0 then 0x00000010 else 0;
  var b28 := if (x & 0x10000000) != 0 then 0x00000008 else 0;
  var b29 := if (x & 0x20000000) != 0 then 0x00000004 else 0;
  var b30 := if (x & 0x40000000) != 0 then 0x00000002 else 0;
  var b31 := if (x & 0x80000000) != 0 then 0x00000001 else 0;

  b0 | b1 | b2 | b3 | b4 | b5 | b6 | b7 | b8 | b9 | b10 | b11 | b12 | b13 | b14 | b15 |
  b16 | b17 | b18 | b19 | b20 | b21 | b22 | b23 | b24 | b25 | b26 | b27 | b28 | b29 | b30 | b31
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ReverseBits(n: int) returns (result: int)
  requires ValidInput(n)
  ensures ValidInput(result)
  ensures result == ReverseBits32Spec(n as bv32) as int
// </vc-spec>
// <vc-code>
{
  var temp: bv32 := n as bv32;
  var res: bv32 := 0;
  var i := 0;

  while i < 32
    invariant 0 <= i <= 32
    invariant temp == (n as bv32) >> i
    invariant res == ReverseBits32Spec((n as bv32) & ((1 << i) - 1)) >> (32 - i)
  {
    res := (res << 1) | (temp & 1);
    temp := temp >> 1;
    i := i + 1;
  }

  result := res as int;
}
// </vc-code>
