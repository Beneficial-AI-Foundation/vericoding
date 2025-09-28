// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fix type conversion and ensure proper bitvector operations */
function SwapMasks(x: bv8, y: bv8): (bv8, bv8)
  ensures var (a, b) := SwapMasks(x, y); a == y && b == x
{
  var diffMask := x ^ y;
  (x ^ diffMask, y ^ diffMask)
}

function ToBv8(n: nat): bv8
  requires n < 256
  ensures ToBv8(n) as int == n
{
  n as bv8
}

function FromBv8(b: bv8): int
  ensures FromBv8(b) == b as int
{
  b as int
}
// </vc-helpers>

// <vc-spec>
method SwapBitvectors(x: int, y: int) returns (result: (int, int))
    requires 0 <= x < 256 && 0 <= y < 256
    ensures result.0 == y && result.1 == x
    ensures x != y ==> (result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Use proper type conversions with helper functions */
{
    var x_bv: bv8 := ToBv8(x);
    var y_bv: bv8 := ToBv8(y);
    var (x_new_bv, y_new_bv) := SwapMasks(x_bv, y_bv);
    result := (FromBv8(x_new_bv), FromBv8(y_new_bv));
}
// </vc-code>
