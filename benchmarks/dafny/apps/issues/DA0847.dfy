// <vc-preamble>
predicate ValidInput(n: int) {
  0 <= n < 0x100000000  // n fits in bv32 (2^32)
}

function PopCount(num: bv32): int
  ensures 0 <= PopCount(num) <= 32
  ensures num != 0 ==> PopCount(num) == 1 + PopCount(num & (num - 1))
  decreases num
{
  if num == 0 then 0
  else 1 + PopCount(num & (num - 1))
}

function CountBitsSpec(n: int): int
  requires ValidInput(n)
  ensures 0 <= CountBitsSpec(n) <= 32
{
  PopCount(n as bv32)
}
// </vc-preamble>

// <vc-helpers>
function CountBitsHelper(num: bv32, count: int): int
  requires count >= 0
  ensures CountBitsHelper(num, count) >= count
  ensures CountBitsHelper(num, count) == count + PopCount(num)
  decreases num
{
  if num == 0 then 
    count
  else 
    assert num & (num - 1) < num;  // helps with termination proof
    assert PopCount(num) == 1 + PopCount(num & (num - 1));  // key relationship
    CountBitsHelper(num & (num - 1), count + 1)
}
// </vc-helpers>

// <vc-spec>
method CountBits(n: int) returns (result: int)
  requires ValidInput(n)
  ensures result == CountBitsSpec(n)
  ensures 0 <= result <= 32
// </vc-spec>
// <vc-code>
{
  result := CountBitsHelper(n as bv32, 0);
}
// </vc-code>
